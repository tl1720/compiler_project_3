// [NYU/Courant Institute] Compiler Construction Project Milestone 3 -*-hacs-*-
//
// SUBSCRIPT TO MINARM32 COMPILER
//
// This is a HACS script that compiles input SubScript files to MinARM32 assembler.
//
// Contents:
// 1. Main Compilation Entry Point
// 2. SubScript grammar
// 3. MinARM32 assembler grammar
// 4. Analysis Utilities
// 5. SubScript Type Analysis
// 6. SubScript to MinARM32 Compiler
//
// This file is © Kristoffer H. Rose <krisrose@crsx.org>
// and licensed under CC-BY-4.0 (https://creativecommons.org/licenses/by/4.0/legalcode).

module edu.nyu.cs.cc.Pr3Base {
  
  ////////////////////////////////////////////////////////////////////////
  // 1. MAIN COMPILATION ENTRY POINT
  ////////////////////////////////////////////////////////////////////////

  sort ARM | scheme Compile(Program);
  Compile(#P) →    CP(Check(#P));  // type check then pass to code generator
  
  ////////////////////////////////////////////////////////////////////////
  // 2. SUBSCRIPT GRAMMAR
  ////////////////////////////////////////////////////////////////////////

  // Implements the grammar of SubScript as described in
  // pr1: http://cs.nyu.edu/courses/spring16/CSCI-GA.2130-001/project1/pr1.pdf

  ////////////////////////////////////////////////////////////////////////
  // LEXICAL CONVENTIONS (pr1:1.1).

  // Ignore:
  space [ \t\n\r] | "//" .*			// white space
    | "/*" ( [^*] | ("*")+ [^/] )* "*/"	 ;	// non-nested C comments

  // We have identifiers, integers, and strings.
  token IDENTIFIER  | ⟨LetterEtc⟩ (⟨LetterEtc⟩ | ⟨Digit⟩)* ;
  token INTEGER	    | ⟨Digit⟩+ ;
  token STRING	    | "\'" ( [^\'\\\n] | \\ ⟨Escape⟩ )* "\'"
    | "\"" ( [^\"\\\n] | \\ ⟨Escape⟩ )* "\""
    ;

  // Lexical helpers.
  token fragment Letter	    | [A-Za-z] ;
  token fragment LetterEtc  | ⟨Letter⟩ | [$_] ;
  token fragment Digit	    | [0-9] ;
  token fragment Escape	 | [\n\\nt''""] | "x" ⟨Hex⟩ ⟨Hex⟩ ;
  token fragment Hex	 | [0-9A-Fa-f] ;

  ////////////////////////////////////////////////////////////////////////
  // EXPRESSIONS (pr1:1.2).
  //
  // Each operator is assigned a HACS precedence following pr1:Figure 1.

  sort Expression

    |  ⟦ ⟨IDENTIFIER⟩ ⟧@13
    |  ⟦ ⟨STRING⟩ ⟧@13
    |  ⟦ ⟨INTEGER⟩ ⟧@13
    |  sugar ⟦ ( ⟨Expression#e⟩ ) ⟧@13 → #e

    |  ⟦ ⟨Expression@12⟩ . ⟨IDENTIFIER⟩ ⟧@12
    |  ⟦ ⟨Expression@12⟩ ( ⟨ExpressionList⟩ ) ⟧@12

    |  ⟦ ! ⟨Expression@11⟩ ⟧@11
    |  ⟦ ~ ⟨Expression@11⟩ ⟧@11
    |  ⟦ - ⟨Expression@11⟩ ⟧@11
    |  ⟦ + ⟨Expression@11⟩ ⟧@11

    |  ⟦ ⟨Expression@10⟩ * ⟨Expression@11⟩ ⟧@10
    |  ⟦ ⟨Expression@10⟩ / ⟨Expression@11⟩ ⟧@10
    |  ⟦ ⟨Expression@10⟩ % ⟨Expression@11⟩ ⟧@10

    |  ⟦ ⟨Expression@9⟩ + ⟨Expression@10⟩ ⟧@9
    |  ⟦ ⟨Expression@9⟩ - ⟨Expression@10⟩ ⟧@9

    |  ⟦ ⟨Expression@9⟩ < ⟨Expression@9⟩ ⟧@8
    |  ⟦ ⟨Expression@9⟩ > ⟨Expression@9⟩ ⟧@8
    |  ⟦ ⟨Expression@9⟩ <= ⟨Expression@9⟩ ⟧@8
    |  ⟦ ⟨Expression@9⟩ >= ⟨Expression@9⟩ ⟧@8

    |  ⟦ ⟨Expression@8⟩ == ⟨Expression@8⟩ ⟧@7
    |  ⟦ ⟨Expression@8⟩ != ⟨Expression@8⟩ ⟧@7

    |  ⟦ ⟨Expression@6⟩ & ⟨Expression@7⟩ ⟧@6
    |  ⟦ ⟨Expression@5⟩ ^ ⟨Expression@6⟩ ⟧@5
    |  ⟦ ⟨Expression@4⟩ | ⟨Expression@5⟩ ⟧@4

    |  ⟦ ⟨Expression@3⟩ && ⟨Expression@4⟩ ⟧@3
    |  ⟦ ⟨Expression@2⟩ || ⟨Expression@3⟩ ⟧@2

    |  ⟦ ⟨Expression@2⟩ ? ⟨Expression⟩ : ⟨Expression@1⟩ ⟧@1

    |  ⟦ ⟨Expression@1⟩ = ⟨Expression⟩ ⟧
    |  ⟦ ⟨Expression@1⟩ += ⟨Expression⟩ ⟧
    |  ⟦ ⟨Expression@1⟩ = { ⟨KeyValueList⟩ } ⟧
    ;

  // Helper to describe actual list of arguments of function call.
  sort ExpressionList | ⟦ ⟨Expression⟩ ⟨ExpressionListTail⟩ ⟧  |  ⟦⟧ ;
  sort ExpressionListTail | ⟦ , ⟨Expression⟩ ⟨ExpressionListTail⟩ ⟧  |	⟦⟧ ;

  // Helper to describe list of key-value pairs.
  sort KeyValueList  |	⟦ ⟨KeyValue⟩ ⟨KeyValueListTail⟩ ⟧  |  ⟦⟧ ;
  sort KeyValueListTail	  |  ⟦ , ⟨KeyValue⟩ ⟨KeyValueListTail⟩ ⟧  |  ⟦⟧ ;
  sort KeyValue	      |	 ⟦ ⟨IDENTIFIER⟩ : ⟨Expression⟩ ⟧ ;

  ////////////////////////////////////////////////////////////////////////
  // TYPES (pr1:1.3).
  //
  // Covers the cases of pr1:Figure 2.

  sort Type
    |  ⟦ boolean ⟧
    |  ⟦ number ⟧
    |  ⟦ string ⟧
    |  ⟦ void ⟧
    |  ⟦ ⟨IDENTIFIER⟩ ⟧
    |  ⟦ ( ⟨TypeList⟩ ) => ⟨Type⟩ ⟧
    |  ⟦ { ⟨NameTypeList⟩ } ⟧
    ;

  // Helper to describe list of types of arguments of function call.
  sort TypeList | ⟦ ⟨Type⟩ ⟨TypeListTail⟩ ⟧ |  ⟦⟧ ;
  sort TypeListTail | ⟦ , ⟨Type⟩ ⟨TypeListTail⟩ ⟧ | ⟦⟧ ;

  // Helper to describe list of names with types.
  sort NameTypeList  |	⟦ ⟨NameType⟩ ⟨NameTypeListTail⟩ ⟧  |  ⟦⟧ ;
  sort NameTypeListTail	  |  ⟦ , ⟨NameType⟩ ⟨NameTypeListTail⟩ ⟧  |  ⟦⟧ ;
  sort NameType	      |	 ⟦ ⟨IDENTIFIER⟩ : ⟨Type⟩ ⟧ ;

  ////////////////////////////////////////////////////////////////////////
  // STATEMENTS (pr1:1.4)
  //
  // Cases from pr1:Figure 3. Dangling else handled with LL order trick from class slides.

  sort Statement
    |  ⟦ { ⟨Statements⟩ } ⟧
    |  ⟦ var ⟨NameType⟩ ; ⟧
    |  ⟦ ⟨Expression⟩ ; ⟧
    |  ⟦ ; ⟧
    |  ⟦ if ( ⟨Expression⟩ ) ⟨IfTail⟩ ⟧
    |  ⟦ while ( ⟨Expression⟩ ) ⟨Statement⟩ ⟧
    |  ⟦ return ⟨Expression⟩ ; ⟧
    |  ⟦ return ; ⟧
    ;

  // Helper to describe sequence of statements.
  sort Statements | ⟦ ⟨Statement⟩ ⟨Statements⟩ ⟧   |  ⟦⟧ ;

  // Helper to combine including and excluding else part.
  sort IfTail | ⟦ ⟨Statement⟩ else ⟨Statement⟩ ⟧  | ⟦ ⟨Statement⟩ ⟧ ;  // eagerly consume elses

  ////////////////////////////////////////////////////////////////////////
  // DECLARATIONS (pr1:1.5).
  //
  // Straight encoding.
  
  sort Declaration
    |  ⟦ interface ⟨IDENTIFIER⟩ { ⟨Members⟩ } ⟧
    |  ⟦ function ⟨IDENTIFIER⟩ ⟨CallSignature⟩ { ⟨Statements⟩ } ⟧
    ;

  // Helper to describe list of members, with scheme to insert missing ;s.
  sort Members	|  ⟦ ⟨Member⟩ ⟨Members⟩ ⟧    |	⟦⟧ ;
  sort OptionalSemicolon | ⟦;⟧ | scheme ⟦⟧; ⟦⟧ → ⟦;⟧ ;

  sort Member
    |  ⟦ ⟨IDENTIFIER⟩ : ⟨Type⟩ ; ⟧
    |  ⟦ ⟨IDENTIFIER⟩ ⟨CallSignature⟩ { ⟨Statements⟩ } ⟨OptionalSemicolon⟩ ⟧
    ;

  sort CallSignature  |	 ⟦ ( ⟨NameTypeList⟩ ) : ⟨Type⟩ ⟧ ;

  ////////////////////////////////////////////////////////////////////////
  // PROGRAM (pr1:1.6).
  //
  // Straight encoding, using Unit for the combination of statements and declarations,
  // with at least one Unit. Program is main input sort.

  main sort Program  |	⟦ ⟨Units⟩ ⟧ ;

  sort Units  |	 ⟦ ⟨Unit⟩ ⟨Units⟩ ⟧  |	⟦ ⟨Unit⟩ ⟧ ;
  sort Unit  |	⟦ ⟨Declaration⟩ ⟧  |  ⟦ ⟨Statement⟩ ⟧ ;

  ////////////////////////////////////////////////////////////////////////
  // 3. MINARM32 ASSEMBLER GRAMMAR
  ////////////////////////////////////////////////////////////////////////

  // Implements the grammar described in
  // arm: http://cs.nyu.edu/courses/spring16/CSCI-GA.2130-001/MinARM32.pdf

  sort ARM | ⟦ ⟨Instruction⟩ ⟨ARM⟩ ⟧ | ⟦⟧ ;

  // Directives (arm:2.1).
  sort Instruction
    | ⟦  DEF ⟨Label⟩ = ⟨INTEGER⟩ ¶⟧	// constant label
    | ⟦⟨Label⟩ : ¶⟧			// define address label
    | ⟦  DCS ⟨STRING⟩ ¶⟧		// static string
    | ⟦  DCI ⟨INTEGER⟩ ¶⟧		// static integer
    | ⟦  ⟨Op⟩ ¶⟧			// machine instruction opcode
    ;

  // Instruction opcodes (arm:2.2).

  sort Reg	| ⟦R0⟧ | ⟦R1⟧ | ⟦R2⟧ | ⟦R3⟧ | ⟦R4⟧ | ⟦R5⟧ | ⟦R6⟧ | ⟦R7⟧
		| ⟦R8⟧ | ⟦R9⟧ | ⟦R10⟧ | ⟦R11⟧ | ⟦R12⟧ | ⟦SP⟧ | ⟦LR⟧ | ⟦PC⟧ ;

  sort Label | symbol ⟦⟨IDENTIFIER⟩⟧ ;  // labels must be treated as identifiers

  sort Arg | ⟦⟨Constant⟩⟧ | ⟦⟨Reg⟩⟧ | ⟦⟨Reg⟩, LSL ⟨Constant⟩⟧ | ⟦⟨Reg⟩, LSR ⟨Constant⟩⟧ ;

  sort Constant | ⟦#⟨INTEGER⟩⟧ | ⟦&⟨Label⟩⟧ ;

  // Data Processing (arm:2.2.1)

  sort Op
    | ⟦MOV ⟨Reg⟩, ⟨Arg⟩ ⟧		// move
    | ⟦MVN ⟨Reg⟩, ⟨Arg⟩ ⟧		// move not
    | ⟦ADD ⟨Reg⟩, ⟨Reg⟩, ⟨Arg⟩ ⟧	// add
    | ⟦SUB ⟨Reg⟩, ⟨Reg⟩, ⟨Arg⟩ ⟧	// subtract
    | ⟦RSB ⟨Reg⟩, ⟨Reg⟩, ⟨Arg⟩ ⟧	// reverse subtract
    | ⟦AND ⟨Reg⟩, ⟨Reg⟩, ⟨Arg⟩ ⟧	// bitwise and
    | ⟦ORR ⟨Reg⟩, ⟨Reg⟩, ⟨Arg⟩ ⟧	// bitwise or
    | ⟦EOR ⟨Reg⟩, ⟨Reg⟩, ⟨Arg⟩ ⟧	// bitwise exclusive or
    | ⟦MUL ⟨Reg⟩, ⟨Reg⟩, ⟨Reg⟩ ⟧	// multiply
    ;

  // Load and Store (arm:2.2.2)

  sort Op
    | ⟦LDR ⟨Reg⟩, ⟨Mem⟩ ⟧		// load register from memory
    | ⟦STR ⟨Reg⟩, ⟨Mem⟩ ⟧		// store register to memory
    | ⟦LDRB ⟨Reg⟩, ⟨Mem⟩ ⟧		// load least byte of register from memory
    | ⟦STRB ⟨Reg⟩, ⟨Mem⟩ ⟧		// store least byte of register to memory
    ;

  sort Mem | ⟦[⟨Reg⟩, ⟨MemOffset⟩]⟧ ;
  sort MemOffset | ⟦⟨Constant⟩⟧ | ⟦⟨Sign⟩⟨Reg⟩, LSL ⟨Constant⟩⟧ | ⟦⟨Sign⟩⟨Reg⟩, LSR ⟨Constant⟩⟧ ;
  sort Sign | ⟦+⟧ | ⟦-⟧ | ⟦⟧ ;

  // Load and Store Multiple (arm:2.2.3)

  sort Op
    | ⟦LDMFD ⟨Reg⟩! , {⟨MReg⟩} ⟧	// load multiple fully descending (pop)
    | ⟦STMFD ⟨Reg⟩! , {⟨MReg⟩} ⟧	// store multiple fully descending (push)
    ;

  sort MReg | ⟦⟨Reg⟩⟧ | ⟦⟨Reg⟩-⟨Reg⟩⟧ | ⟦⟨Reg⟩, ⟨MReg⟩⟧ | ⟦⟨Reg⟩-⟨Reg⟩, ⟨MReg⟩⟧ ;

  // Compare (arm:2.2.4)

  sort Op
    | ⟦CMP ⟨Reg⟩, ⟨Arg⟩ ⟧		// compare
    ;

  // Branching (arm:2.5).

  sort Op
    | ⟦B ⟨Label⟩ ⟧			// branch always
    | ⟦BEQ ⟨Label⟩ ⟧			// branch if equal
    | ⟦BNE ⟨Label⟩ ⟧			// branch if not equal
    | ⟦BGT ⟨Label⟩ ⟧			// branch if greater than
    | ⟦BLT ⟨Label⟩ ⟧			// branch if less than
    | ⟦BGE ⟨Label⟩ ⟧			// branch if greater than or equal
    | ⟦BLE ⟨Label⟩ ⟧			// branch if less than or equal
    | ⟦BL ⟨Label⟩ ⟧			// branch and link
    ;

  ////////////////////////////////////////////////////////////////////////
  // 4. ANALYSIS UTILITIES
  ////////////////////////////////////////////////////////////////////////

  // Make sure Computed is loaded by having a direct computed scheme [sic].
  sort Computed | scheme ComputedLoader();

  ////////////////////////////////////////////////////////////////////////
  // Generic Utilities.
  
  // Booleans.
  
  sort Bool | False | True;
  | scheme Not(Bool); Not(False) → True; Not(True) → False;
  | scheme And(Bool, Bool); And(False, #2) → False; And(True, #2) → #2;
  | scheme Or(Bool, Bool); Or(False, #2) → #2; Or(True, #2) → True;

  ////////////////////////////////////////////////////////////////////////
  // SubScript Utilities.

  // Lists.
  
  // Ns: list of names with IsEmpty*, Append*, Contains*, Distinct*.
  sort Ns | NoNs | MoNs(IDENTIFIER, Ns);
  //
  sort Bool | scheme IsEmptyNs(Ns); IsEmptyNs(NoNs) → True; IsEmptyNs(MoNs(#ID, #)) → False;
  //
  sort Ns | scheme AppendNs(Ns, Ns);
  AppendNs(NoNs, #) → #;
  AppendNs(MoNs(#ID, #1), #2) → MoNs(#ID, AppendNs(#1, #2));
  //
  sort Bool | scheme ContainsNs(Ns, IDENTIFIER) ;
  ContainsNs(NoNs, #ID) → False ;
  [data #ID] ContainsNs(MoNs(#ID, #), #ID) → True ;
  default ContainsNs(MoNs(#ID1, #), #ID2) → ContainsNs(#, #ID2) ;
  //
  sort Bool | scheme DistinctNs(Ns) ;
  DistinctNs(#) → DistinctNs1(#) ;
  {
    attribute ↓setNs{IDENTIFIER} ; // set helper to capture passed names
    sort Bool | scheme DistinctNs1(Ns) ↓setNs ;
    DistinctNs1(NoNs) → True ;
    DistinctNs1(MoNs(#ID, #)) ↓setNs{¬#ID} → DistinctNs1(#) ↓setNs{#ID} ;
    DistinctNs1(MoNs(#ID, #)) ↓setNs{#ID} → False ;
  }

  // Ts: list of types with IsEmpty*, Append*.
  sort Ts | NoTs | MoTs(Type, Ts);
  sort Bool | scheme IsEmptyTs(Ts); IsEmptyTs(NoTs) → True; IsEmptyTs(MoTs(#ID, #)) → False;
  sort Ts | scheme AppendTs(Ts, Ts);
  AppendTs(NoTs, #) → #;
  AppendTs(MoTs(#T, #1), #2) → MoTs(#T, AppendTs(#1, #2));

  // NTs: lists of name-type pairs with IsEmpty*, Append*, Keys*, Values*, Lookup*.
  sort NTs | NoNTs | MoNTs(IDENTIFIER, Type, NTs);
  //
  sort Bool | scheme IsEmptyNTs(NTs);
  IsEmptyNTs(NoNTs) → True; IsEmptyNTs(MoNTs(#ID, #T, #)) → False;
  //
  sort NTs | scheme AppendNTs(NTs, NTs);
  AppendNTs(NoNTs, #) → # ;
  AppendNTs(MoNTs(#ID, #T, #1), #2) → MoNTs(#ID, #T, AppendNTs(#1, #2)) ;
  //
  sort Ns | scheme KeysNTs(NTs) ;
  KeysNTs(NoNTs) → NoNs ;
  KeysNTs(MoNTs(#ID, #T, #)) → MoNs(#ID, KeysNTs(#)) ;
  //
  sort Ts | scheme ValuesNTs(NTs) ;
  ValuesNTs(NoNTs) → NoTs ;
  ValuesNTs(MoNTs(#ID, #T, #)) → MoTs(#T, ValuesNTs(#)) ;
  //
  sort Type | scheme LookupNTs(NTs, IDENTIFIER) ;
  LookupNTs(NoNTs, #ID) → ⟦void⟧ ;
  [data #ID] LookupNTs(MoNTs(#ID, #T, #), #ID) → #T ;
  default LookupNTs(MoNTs(#ID1, #T, #), #ID2) → LookupNTs(#, #ID2) ;
  
  // Type utilities.

  // MkFunctionType: create function type from list of argument types and return type.
  sort Type | scheme MkFunctionType(Ts, Type) ;
  MkFunctionType(#Ts, #T) → ⟦ ( ⟨TypeList MkFunctionType1(#Ts)⟩ ) => ⟨Type#T⟩ ⟧ ;
  {
    sort TypeList | scheme MkFunctionType1(Ts) ;
    MkFunctionType1(NoTs) → ⟦ ⟧ ;
    MkFunctionType1(MoTs(#T, #Ts)) → ⟦ ⟨Type#T⟩ ⟨TypeListTail MkFunctionType2(#Ts)⟩ ⟧ ;
    sort TypeListTail | scheme MkFunctionType2(Ts) ;
    MkFunctionType2(NoTs) → ⟦ ⟧ ;
    MkFunctionType2(MoTs(#T, #Ts)) → ⟦ , ⟨Type#T⟩ ⟨TypeListTail MkFunctionType2(#Ts)⟩ ⟧ ;
  }

  // ReturnType: extract return type from function type.
  sort Type | scheme ReturnType(Type) ;
  ReturnType(⟦ ( ⟨TypeList#1⟩ ) => ⟨Type#2⟩ ⟧) → #2 ;
  //default ReturnType(#) → # ;

  // ArgumentTypes: extract function argument types as list.
  sort Ts | scheme ArgumentTypes(Type) ;
  ArgumentTypes(⟦ ( ⟨TypeList#1⟩ ) => ⟨Type#2⟩ ⟧) → TypeListTypes(#1) ;
  //default ArgumentTypes(#) → MoTs(⟦void⟧, NoTs) ; // type that will always fail to match

  | scheme TypeListTypes(TypeList) ;
  TypeListTypes(⟦ ⟧) → NoTs ;
  TypeListTypes(⟦ ⟨Type#1⟩ ⟨TypeListTail#2⟩ ⟧) → MoTs(#1, TypeListTailTypes(#2)) ;

  | scheme TypeListTailTypes(TypeListTail) ;
  TypeListTailTypes(⟦ ⟧) → NoTs ;
  TypeListTailTypes(⟦ , ⟨Type#1⟩ ⟨TypeListTail#2⟩ ⟧) → MoTs(#1, TypeListTailTypes(#2)) ;

  // MkRecordType: assemble record type from NTs.
  sort Type | scheme MkRecordType(NTs) ;
  MkRecordType(#) → ⟦ { ⟨NameTypeList MkRecordType1(#)⟩ } ⟧ ;
  {
    sort NameTypeList | scheme MkRecordType1(NTs) ;
    MkRecordType1(NoNTs) → ⟦ ⟧ ;
    MkRecordType1(MoNTs(#ID, #T, #)) → ⟦ ⟨IDENTIFIER#ID⟩ : ⟨Type#T⟩ ⟨NameTypeListTail MkRecordType2(#)⟩ ⟧;
    sort NameTypeListTail | scheme MkRecordType2(NTs) ;
    MkRecordType2(NoNTs) → ⟦ ⟧ ;
    MkRecordType2(MoNTs(#ID, #T, #)) → ⟦ , ⟨IDENTIFIER#ID⟩ : ⟨Type#T⟩ ⟨NameTypeListTail MkRecordType2(#)⟩ ⟧;
  }

  // MemberMap: extract list of name-type pairs from record type.
  sort NTs | scheme MemberMap(Type) ;
  MemberMap(⟦ { ⟨NameTypeList#⟩ } ⟧) → NameTypeListMap(#) ;
  //default MemberMap(#) → NoNTs ;

  | scheme NameTypeListMap(NameTypeList) ;
  NameTypeListMap(⟦ ⟧) → NoNTs ;
  NameTypeListMap(⟦ ⟨IDENTIFIER#ID⟩ : ⟨Type#T⟩ ⟨NameTypeListTail#⟩ ⟧) → MoNTs(#ID, #T, NameTypeListTailMap(#)) ;

  | scheme NameTypeListTailMap(NameTypeListTail) ;
  NameTypeListTailMap(⟦ ⟧) → NoNTs ;
  NameTypeListTailMap(⟦ , ⟨IDENTIFIER#ID⟩ : ⟨Type#T⟩ ⟨NameTypeListTail#⟩ ⟧) → MoNTs(#ID, #T, NameTypeListTailMap(#)) ;

  // SubScript Syntax related.
  
  // IsLValue: check whether expression can be used on left side of assignment.
  sort Bool | scheme IsLValue(Expression) ;
  IsLValue(⟦ ⟨IDENTIFIER#1⟩ ⟧) → True ;
  IsLValue(⟦ ⟨Expression#1⟩ . ⟨IDENTIFIER#2⟩ ⟧) → True ;
  default IsLValue(#) → False ;

  // AddKey: Add key of KV pair to an Ns list.
  sort Ns | scheme AddKey(Ns, KeyValue) ;
  AddKey(#Ns, ⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧) → MoNs(#1, #Ns) ;
  default AddKey(#Ns, #) → #Ns ;

  // KeyIn: Check that key from KV pair is in an Ns.
  sort Bool | scheme KeyIn(Ns, KeyValue) ;
  KeyIn(#Ns, ⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧) → ContainsNs(#Ns, #1) ;
  default KeyIn(#Ns, #) → False ;
  
  ////////////////////////////////////////////////////////////////////////
  // MinARM32 Utilities.
  
  // Helper concatenation/flattening of ARM.
  sort ARM | scheme ⟦ { ⟨ARM⟩ } ⟨ARM⟩ ⟧ ;
  ⟦ {} ⟨ARM#⟩ ⟧ → # ;
  ⟦ {⟨Instruction#1⟩ ⟨ARM#2⟩} ⟨ARM#3⟩ ⟧
    → ⟦ ⟨Instruction#1⟩ {⟨ARM#2⟩} ⟨ARM#3⟩ ⟧ ;

  // Helper data structure for list of registers.
  sort Rs | NoRs | MoRs(Reg, Rs) | scheme AppendRs(Rs, Rs) ;
  AppendRs(NoRs, #Rs) → #Rs ;
  AppendRs(MoRs(#Rn, #Rs1), #Rs2) → MoRs(#Rn, AppendRs(#Rs1, #Rs2)) ;

  // Helper conversion from MReg syntax to register list.
  sort Rs | scheme XMReg(MReg) ;
  XMReg(⟦⟨Reg#r⟩⟧) → MoRs(#r, NoRs) ;
  XMReg(⟦⟨Reg#r1⟩-⟨Reg#r2⟩⟧) → XMReg1(#r1, #r2) ;
  XMReg(⟦⟨Reg#r⟩, ⟨MReg#Rs⟩⟧) → MoRs(#r, XMReg(#Rs)) ;
  XMReg(⟦⟨Reg#r1⟩-⟨Reg#r2⟩, ⟨MReg#Rs⟩⟧) → AppendRs(XMReg1(#r1, #r2), XMReg(#Rs)) ;

  | scheme XMReg1(Reg, Reg) ;
  XMReg1(#r, #r) → MoRs(#r, NoRs) ;
  default XMReg1(#r1, #r2) → XMReg2(#r1, #r2) ;

  | scheme XMReg2(Reg, Reg) ;
  XMReg2(⟦R0⟧, #r2) → MoRs(⟦R0⟧, XMReg1(⟦R1⟧, #r2)) ;
  XMReg2(⟦R1⟧, #r2) → MoRs(⟦R1⟧, XMReg1(⟦R2⟧, #r2)) ;
  XMReg2(⟦R2⟧, #r2) → MoRs(⟦R2⟧, XMReg1(⟦R3⟧, #r2)) ;
  XMReg2(⟦R3⟧, #r2) → MoRs(⟦R3⟧, XMReg1(⟦R4⟧, #r2)) ;
  XMReg2(⟦R4⟧, #r2) → MoRs(⟦R4⟧, XMReg1(⟦R5⟧, #r2)) ;
  XMReg2(⟦R5⟧, #r2) → MoRs(⟦R5⟧, XMReg1(⟦R6⟧, #r2)) ;
  XMReg2(⟦R6⟧, #r2) → MoRs(⟦R6⟧, XMReg1(⟦R7⟧, #r2)) ;
  XMReg2(⟦R7⟧, #r2) → MoRs(⟦R7⟧, XMReg1(⟦R8⟧, #r2)) ;
  XMReg2(⟦R8⟧, #r2) → MoRs(⟦R8⟧, XMReg1(⟦R9⟧, #r2)) ;
  XMReg2(⟦R9⟧, #r2) → MoRs(⟦R9⟧, XMReg1(⟦R10⟧, #r2)) ;
  XMReg2(⟦R10⟧, #r2) → MoRs(⟦R10⟧, XMReg1(⟦R11⟧, #r2)) ;
  XMReg2(⟦R11⟧, #r2) → MoRs(⟦R11⟧, XMReg1(⟦R12⟧, #r2)) ;
  XMReg2(⟦R12⟧, #r2) → MoRs(⟦R12⟧, NoRs) ;
  XMReg1(⟦SP⟧, #r2) → error⟦MinARM32 error: Cannot use SP in MReg range.⟧ ;
  XMReg1(⟦LR⟧, #r2) → error⟦MinARM32 error: Cannot use LR in MReg range.⟧ ;
  XMReg1(⟦PC⟧, #r2) → error⟦MinARM32 error: Cannot use PC in MReg range.⟧ ;
  
  // Helper to insert computed assembly constants.
  sort Constant | scheme Immediate(Computed) ;
  Immediate(#x) → ⟦#⟨INTEGER#x⟩⟧ ;

  // Helper to insert instructions to add/subtract a constant.
  sort Instruction | scheme AddConstant(Reg, Reg, Computed) ;
  AddConstant(#Rd, #Rn, #x)
    → AddConstant1(#x,
		   ⟦ ADD ⟨Reg#Rd⟩, ⟨Reg#Rn⟩, ⟨Constant Immediate(#x)⟩ ⟧,
		   ⟦ SUB ⟨Reg#Rd⟩, ⟨Reg#Rn⟩, ⟨Constant Immediate(⟦0 - #x⟧)⟩ ⟧) ;
  | scheme AddConstant1(Computed, Instruction, Instruction) ;
  AddConstant1(#x, #pos, #neg) → AddConstant2(⟦ #x ≥ 0 ? #pos : #neg ⟧) ;
  | scheme AddConstant2(Computed) ;
  AddConstant2(#add) → #add ;
  
  ////////////////////////////////////////////////////////////////////////
  // 5. SUBSCRIPT TYPE ANALYSIS
  ////////////////////////////////////////////////////////////////////////

  // Implements the SDD in
  // sdd: http://cs.nyu.edu/courses/spring16/CSCI-GA.2130-001/project2/Pr2Rose-SDD.pdf

  // Stand-alone type checker script.
  sort Program | scheme Check(Program)  | scheme Check2(Program);
  Check(#P) → Check2(Pok(#P)); // use inheritance bootstrap scheme
  Check2(#P ↑ok(True))  → #P;
  Check2(#P ↑ok(False))  → Dump(#P) ;
  | scheme Dump(Program) ; // undefined!
  
  ////////////////////////////////////////////////////////////////////////
  // Attributes (sdd:1.8)

  attribute ↑ok(Bool);				// whether entire subtree is well typed.
  attribute ↑t(Type);				// type of node
  
  attribute ↑ds(NTs);				// declarations from node
  attribute ↑uds(NTs);				// top level declaration of statement
  attribute ↓te{IDENTIFIER : Type};		// type environment
  attribute ↑ts(Ts);				// list of types in declarations
  attribute ↓rt(Type);				// current return type
  attribute ↓r{IDENTIFIER : Type};		// record member types
  attribute ↓ums(Ns);				// used member names

  ////////////////////////////////////////////////////////////////////////
  // P (Program).
  
  sort Program | ↑ok | scheme Pok(Program); // with inheritance bootstrap scheme
  
  // P → Us1

  // | Us1.te = Extend(GlobalDefs, Us1.ds)
  Pok(⟦ ⟨Units#1 ↑ds(#Us1ds)⟩ ⟧↑#) → ⟦ ⟨Units UsteExtend(#1, AppendNTs(GlobalDefs, #Us1ds))⟩ ⟧↑# ;

  // | P.ok = DistinctFirst(Us1.ds) ∧ Us1.ok
  ⟦ ⟨Units#1 ↑ds(#Us1ds) ↑ok(#Us1ok)⟩ ⟧ ↑ok(And(DistinctNs(KeysNTs(#Us1ds)), #Us1ok));

  ////////////////////////////////////////////////////////////////////////
  // Us (Units).

  sort Units | ↑ds | scheme Uste(Units) ↓te | ↑ok ;

  // Cascade helper to initialize Uste type environment propagation below.
  | scheme UsteExtend(Units, NTs) ↓te;
  UsteExtend(#1, NoNTs) ↓te{:#te} → Uste(#1) ↓te{:#te} ;
  UsteExtend(#1, MoNTs(#ID, #T, #2)) → UsteExtend(#1, #2) ↓te{#ID : #T} ;

  // Us → U1 Us2

  // | Us.ds = U1.ds ∥ Us2.ds
  ⟦ ⟨Unit#1 ↑ds(#U1ds)⟩  ⟨Units#2 ↑ds(#Us2ds)⟩ ⟧ ↑ds(AppendNTs(#U1ds, #Us2ds));
  
  // | U1.te = Us.te
  // | Us2.te = Extend(Us.te, U1.uds)
  Uste(⟦ ⟨Unit#1 ↑uds(#U1uds)⟩  ⟨Units#2⟩ ⟧↑#) ↓te{:#te} →  ⟦ ⟨Unit Ute(#1) ↓te{:#te}⟩  ⟨Units UsteExtend(#2, #U1uds) ↓te{:#te}⟩ ⟧↑#;

  // | Us.ok = U1.ok ∧ Us2.ok
  ⟦ ⟨Unit#1 ↑ok(#U1ok)⟩  ⟨Units#2 ↑ok(#Us2ok)⟩ ⟧ ↑ok(And(#U1ok, #Us2ok));

  // Us → U1

  // | Us.ds = U1.ds
  ⟦ ⟨Unit#1 ↑ds(#U1ds)⟩ ⟧ ↑ds(#U1ds);
  
  // | U1.te = Us.te
  Uste(⟦ ⟨Unit#1⟩ ⟧↑#) ↓te{:#te} → ⟦ ⟨Unit Ute(#1) ↓te{:#te}⟩ ⟧↑# ;
  
  // | Us.ok = U1.ok
  ⟦ ⟨Unit#1 ↑ok(#U1ok)⟩ ⟧ ↑ok(#U1ok);

  ////////////////////////////////////////////////////////////////////////
  // U (Unit)

  sort Unit | ↑ds | ↑uds | scheme Ute(Unit) ↓te | ↑ok ;

  // U → D1

  // | U.ds = D1.ds
  ⟦ ⟨Declaration#1 ↑ds(#D1ds)⟩ ⟧ ↑ds(#D1ds);
  
  // | U.uds = ε
  ⟦ ⟨Declaration#1⟩ ⟧ ↑uds(NoNTs);
  
  // | D1.te = U.te
  Ute(⟦ ⟨Declaration#1⟩ ⟧↑#) ↓te{:#te} → ⟦ ⟨Declaration Dte(#1) ↓te{:#te}⟩ ⟧ ↑# ;
  
  // | U.ok = D1.ok
  ⟦ ⟨Declaration#1 ↑ok(#D1ok)⟩ ⟧ ↑ok(#D1ok);

  // U → S1

  // | U.ds = ε
  ⟦ ⟨Statement#1⟩ ⟧ ↑ds(NoNTs);
  
  // | U.uds = S1.ds
  ⟦ ⟨Statement#1 ↑ds(#S1ds)⟩ ⟧ ↑uds(#S1ds);

  // | S1.te = U.te
  // | S1.rt = void
  Ute(⟦ ⟨Statement#1⟩ ⟧↑#) ↓te{:#te} → ⟦ ⟨Statement Stert(#1) ↓te{:#te} ↓rt(⟦ void ⟧)⟩ ⟧↑# ;
  
  // | U.ok = S1.ok
  ⟦ ⟨Statement#1 ↑ok(#S1ok)⟩ ⟧ ↑ok(#S1ok);

  ////////////////////////////////////////////////////////////////////////
  // D (Declaration)
  
  sort Declaration | ↑ds | scheme Dte(Declaration) ↓te | ↑ok ;
  
  // D → interface id1 { Ms2 }

  // | D.ds = (id1.sym, { Ms2.ds })
  ⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2 ↑ds(#Ms2ds)⟩ } ⟧ ↑ds(MoNTs(#1, MkRecordType(#Ms2ds), NoNTs)) ;

  // | Ms2.te = D.te
  Dte(⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2⟩ } ⟧↑#) ↓te{:#te} → ⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members Mste(#2) ↓te{:#te}⟩ } ⟧↑# ;
  
  // | D.ok = DistinctFirst(Ms2.ds) ∧ Ms2.ok
  ⟦ interface ⟨IDENTIFIER#1⟩ { ⟨Members#2 ↑ds(#Ms2ds) ↑ok(#Ms2ok)⟩ } ⟧ ↑ok(And(DistinctNs(KeysNTs(#Ms2ds)), #Ms2ok)) ;

  // D → function id1 CS2 { Ss3 }

  // | D.ds = (id1.sym, CS2.t)
  ⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑t(#CS2t)⟩ { ⟨Statements#3⟩ } ⟧ ↑ds(MoNTs(#1, #CS2t, NoNTs)) ;
  
  // | Ss3.te = Extend(D.te, CS2.ds)
  // | Ss3.rt = ReturnType(CS2.t)
  Dte(⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#CS2ds) ↑t(#CS2t)⟩ { ⟨Statements#3⟩ } ⟧↑#) ↓te{:#te}
  → ⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2⟩ { ⟨Statements SstertExtend(#3, #CS2ds) ↓te{:#te} ↓rt(ReturnType(#CS2t))⟩ } ⟧↑# ;
  
  // | D.ok = DistinctFirst(CS2.ds) ∧ Ss3.ok
  ⟦ function ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#CS2ds)⟩ { ⟨Statements#3 ↑ok(#Ss3ok)⟩ } ⟧
    ↑ok(And(DistinctNs(KeysNTs(#CS2ds)), #Ss3ok)) ;

  ////////////////////////////////////////////////////////////////////////
  // Ms (Members)

  sort Members | ↑ds | scheme Mste(Members) ↓te | ↑ok ;

  // Ms → M1 Ms2

  // | Ms.ds = M1.ds ∥ Ms2.ds
  ⟦ ⟨Member#1 ↑ds(#M1ds)⟩ ⟨Members#2 ↑ds(#Ms2ds)⟩ ⟧ ↑ds(AppendNTs(#M1ds, #Ms2ds)) ;

  // | M1.te = Ms2.te = Ms.te
  Mste(⟦ ⟨Member#1⟩ ⟨Members#2⟩ ⟧↑#) ↓te{:#te} → ⟦ ⟨Member Mte(#1) ↓te{:#te}⟩ ⟨Members Mste(#2) ↓te{:#te}⟩ ⟧↑# ;
  
  // | Ms.ok = M1.ok ∧ Ms2.ok
  ⟦ ⟨Member#1 ↑ok(#M1ok)⟩ ⟨Members#2 ↑ok(#Ms2ok)⟩ ⟧ ↑ok(And(#M1ok, #Ms2ok)) ;

  // Ms → ε
  Mste(⟦⟧↑#) → ⟦⟧↑# ; // dummy case

  // | Ms.ds = ε
  ⟦⟧ ↑ds(NoNTs) ;

  // | Ms.ok = True
  ⟦⟧ ↑ok(True) ;

  ////////////////////////////////////////////////////////////////////////
  // M (Member)

  sort Member | ↑ds | scheme Mte(Member) | ↑ok ;

  // M → id1 : T2 ;
  Mte(⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧↑#) → ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧↑# ; // dummy case

  // | M.ds = (id1.sym, T2)
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧ ↑ds(MoNTs(#1, #2, NoNTs)) ;

  // | M.ok = True
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ; ⟧ ↑ok(True) ;

  // M → id1 CS2 { Ss3 } ;

  // | M.ds = (id1.sym, CS2.t)
  ⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑t(#CS2t)⟩ { ⟨Statements#3⟩ } ; ⟧ ↑ds(MoNTs(#1, #CS2t, NoNTs)) ;
  
  // | Ss3.te = Extend(M.te, CS2.ds)
  // | Ss3.rt = ReturnType(CS2.t)
  Mte(⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#CS2ds) ↑t(#CS2t)⟩ { ⟨Statements#3⟩ } ; ⟧↑#) ↓te{:#te}
    → ⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2⟩ { ⟨Statements SstertExtend(#3, #CS2ds) ↓te{:#te} ↓rt(ReturnType(#CS2t))⟩ } ; ⟧↑# ;

  // | M.ok = DistinctFirst(CS2.ds) ∧ Ss3.ok
  ⟦ ⟨IDENTIFIER#1⟩ ⟨CallSignature#2 ↑ds(#CS2ds)⟩ { ⟨Statements#3 ↑ok(#Ss3ok)⟩ } ; ⟧
    ↑ok(And(DistinctNs(KeysNTs(#CS2ds)), #Ss3ok)) ;
  
  ////////////////////////////////////////////////////////////////////////
  // CS (CallSignature)

  sort CallSignature | ↑ds | ↑t ;

  // CS → ( NTL1 ) : T2
  
  // | CS.ds = NTL1.ds
  ⟦ ( ⟨NameTypeList#1 ↑ds(#NTL1ds)⟩ ) : ⟨Type#2⟩ ⟧ ↑ds(#NTL1ds) ;

  // | CS.t = ( NTL1.ts ) => T2
  ⟦ ( ⟨NameTypeList#1 ↑ts(#NTL1ts)⟩ ) : ⟨Type#2⟩ ⟧ ↑t(MkFunctionType(#NTL1ts, #2)) ;

  ////////////////////////////////////////////////////////////////////////
  // NTL (NameTypeList)

  sort NameTypeList | ↑ds | ↑ts ;

  // NTL → NT1 NTLT2

  // | NTL.ds = NT1.ds ∥ NTLT2.ds
  ⟦ ⟨NameType#1 ↑ds(#NT1ds)⟩ ⟨NameTypeListTail#2 ↑ds(#NTLT2ds)⟩ ⟧ ↑ds(AppendNTs(#NT1ds, #NTLT2ds)) ;
  
  // | NTL.ts = (NT1.t) ∥ NTLT2.ts
  ⟦ ⟨NameType#1 ↑t(#NT1t)⟩ ⟨NameTypeListTail#2 ↑ts(#NTLT2ts)⟩ ⟧ ↑ts(MoTs(#NT1t, #NTLT2ts)) ;

  // NTL → ε

  // | NTL.ds = ε
  ⟦ ⟧ ↑ds(NoNTs) ;

  // | NTL.ts = ε
  ⟦ ⟧ ↑ts(NoTs) ;

  ////////////////////////////////////////////////////////////////////////
  // NTLT (NameTypeListTail)

  sort NameTypeListTail | ↑ds | ↑ts ;

  // NTLT → , NT1 NTLT2

  // | NTLT.ds = NT1.ds ∥ NTLT2.ds
  ⟦ , ⟨NameType#1 ↑ds(#NT1ds)⟩ ⟨NameTypeListTail#2 ↑ds(#NTLT2ds)⟩ ⟧ ↑ds(AppendNTs(#NT1ds, #NTLT2ds)) ;
  
  // | NTLT.ts = (NT1.t) ∥ NTLT2.ts
  ⟦ , ⟨NameType#1 ↑t(#NT1t)⟩ ⟨NameTypeListTail#2 ↑ts(#NTLT2ts)⟩ ⟧ ↑ts(MoTs(#NT1t, #NTLT2ts)) ;

  // NTLT → ε

  // | NTLT.ds = ε
  ⟦ ⟧ ↑ds(NoNTs) ;

  // | NTLT.ts = ε
  ⟦ ⟧ ↑ts(NoTs) ;

  ////////////////////////////////////////////////////////////////////////
  // NT (NameType)

  sort NameType | ↑ds | ↑t ;

  // NT → id1 : T2

  // | NT.ds = (id1.sym, T2)
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟧ ↑ds(MoNTs(#1, #2, NoNTs)) ;

  // | NT.t = T2
  ⟦ ⟨IDENTIFIER#1⟩ : ⟨Type#2⟩ ⟧ ↑t(#2) ;

  ////////////////////////////////////////////////////////////////////////
  // Ss (Statements)

  sort Statements | Sstert(Statements) ↓te ↓rt | ↑ok ;

  // Ss → S1 Ss2

  // | S1.te = Ss.te
  // | Ss2.te = Extend(Ss.te, S1.ds)
  // | S1.rt = Ss2.rt = Ss.rt
  Sstert(⟦ ⟨Statement#1 ↑ds(#S1ds)⟩ ⟨Statements#2⟩ ⟧↑#) ↓te{:#te} ↓rt(#rt)
    → ⟦ ⟨Statement Stert(#1) ↓te{:#te} ↓rt(#rt)⟩ ⟨Statements SstertExtend(#2, #S1ds) ↓te{:#te} ↓rt(#rt)⟩ ⟧↑# ;

  // | Ss.ok = S1.ok ∧ Ss2.ok
  ⟦ ⟨Statement#1 ↑ok(#S1ok)⟩ ⟨Statements#2 ↑ok(#Ss2ok)⟩ ⟧ ↑ok(And(#S1ok, #Ss2ok));

  // Ss → ε
  Sstert(⟦⟧↑#) → ⟦⟧↑# ; // dummy

  // | Ss.ok = True
  ⟦ ⟧ ↑ok(True) ;

  // Helper to invoke Sstert with list of name-type pairs to add.
  | scheme SstertExtend(Statements, NTs) ↓te ↓rt ;
  SstertExtend(#1, NoNTs) ↓te{:#te} ↓rt(#rt) → Sstert(#1) ↓te{:#te} ↓rt(#rt) ;
  SstertExtend(#1, MoNTs(#N, #T, #2)) ↓te{:#te} ↓rt(#rt) → SstertExtend(#1, #2) ↓te{:#te} ↓rt(#rt) ↓te{#N : #T};
  
  ////////////////////////////////////////////////////////////////////////
  // S (Statement)

  sort Statement | ↑ds | scheme Stert(Statement) ↓te ↓rt | ↑ok ;
  
  // S → { Ss1 }

  // | S.ds = ε
  ⟦ { ⟨Statements#1⟩ } ⟧ ↑ds(NoNTs) ;
  
  // | Ss1.te = S.te
  // | Ss1.rt = S.rt
  Stert(⟦ { ⟨Statements#1⟩ } ⟧↑#) ↓te{:#te} ↓rt(#rt) → ⟦ { ⟨Statements Sstert(#1) ↓te{:#te} ↓rt(#rt)⟩ } ⟧↑# ;
  
  // | S.ok = Ss1.ok
  ⟦ { ⟨Statements#1 ↑ok(#Ss1ok)⟩ } ⟧ ↑ok(#Ss1ok) ;

  // S → var NT1 ;

  // | S.ds = NT1.ds
  ⟦ var ⟨NameType#1 ↑ds(#NT1ds)⟩ ; ⟧ ↑ds(#NT1ds) ;

  // | S.ok = Eq(S.te, NT1.t, NT1.t)
  Stert(⟦ var ⟨NameType#1 ↑t(#NT1t)⟩ ; ⟧↑#) ↓te{:#te} → ⟦ var ⟨NameType#1⟩ ; ⟧↑# ↑ok(Eq(#NT1t, #NT1t) ↓te{:#te}) ;

  // S → E1 ;

  // | S.ds = ε
  ⟦ ⟨Expression#1⟩ ; ⟧ ↑ds(NoNTs) ;
  
  // | E1.te = S.te
  Stert(⟦ ⟨Expression#1⟩ ; ⟧↑#) ↓te{:#te} → ⟦ ⟨Expression Ete(#1) ↓te{:#te}⟩ ; ⟧↑# ;
  
  // | S.ok = E1.ok
  ⟦ ⟨Expression#1 ↑ok(#E1ok)⟩ ; ⟧ ↑ok(#E1ok) ;
  
  // S → ;
  Stert(⟦ ; ⟧↑#) → ⟦ ; ⟧↑# ; // dummy

  // | S.ds = ε
  ⟦ ; ⟧ ↑ds(NoNTs) ;

  // | S.ok = True
  ⟦ ; ⟧ ↑ok(True) ;

  // S → if (E1) IT2

  // | S.ds = ε
  ⟦ if ( ⟨Expression#1⟩ ) ⟨IfTail#2⟩ ⟧ ↑ds(NoNTs) ;

  // | E1.te = IT2.te = S.te
  // | IT2.rt = S.rt
  Stert(⟦ if ( ⟨Expression#1⟩ ) ⟨IfTail#2⟩ ⟧↑#) ↓te{:#te} ↓rt(#rt) → ⟦ if ( ⟨Expression Ete(#1) ↓te{:#te}⟩ ) ⟨IfTail ITtert(#2) ↓te{:#te} ↓rt(#rt)⟩ ⟧↑# ;

  // | S.ok = Eq(S.te, boolean, E1.t) ∧ E1.ok ∧ IT2.ok
  ⟦ if ( ⟨Expression#1 ↑ok(#E1ok) ↑t(#E1t)⟩ ) ⟨IfTail#2 ↑ok(#IT2ok)⟩ ⟧ ↑ok(And(Eq(⟦boolean⟧, #E1t), And(#E1ok, #IT2ok))) ;

  // S → while (E1) S2

  // | S.ds = ε
  ⟦ while ( ⟨Expression#1⟩ ) ⟨Statement#2⟩ ⟧ ↑ds(NoNTs) ;

  // | E1.te = S2.te = S.te
  // | S2.rt = S.rt
  Stert(⟦ while ( ⟨Expression#1⟩ ) ⟨Statement#2⟩ ⟧↑#) ↓te{:#te} ↓rt(#rt) → ⟦ if ( ⟨Expression Ete(#1) ↓te{:#te}⟩ ) ⟨Statement Stert(#2) ↓te{:#te} ↓rt(#rt)⟩ ⟧↑# ;

  // | S.ok = Eq(S.te, boolean, E1.t) ∧ E1.ok ∧ S2.ok
  ⟦ while ( ⟨Expression#1 ↑ok(#E1ok) ↑t(#E1t)⟩ ) ⟨Statement#2 ↑ok(#S2ok)⟩ ⟧ ↑ok(And(Eq(⟦boolean⟧, #E1t), And(#E1ok, #S2ok))) ;

  // S → return E1 ;
    
  // | S.ds = ε
  ⟦ return ⟨Expression#1⟩ ; ⟧ ↑ds(NoNTs) ;

  // | E1.te = S.te
  // | S.ok = E1.ok ∧ Eq(S.te, E1.t, S.rt)
  Stert(⟦ return ⟨Expression#1⟩ ; ⟧↑#) ↓te{:#te} ↓rt(#rt) → StertReturn(⟦ return ⟨Expression Ete(#1) ↓te{:#te}⟩ ; ⟧↑#) ↓rt(#rt) ;
  // Proceed when E1.ok and E1.t, depending on E1.te dispersed above, have been computed.
  | scheme StertReturn(Statement) ↓rt ;
  StertReturn(⟦ return ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ ; ⟧↑#) ↓rt(#rt)
    → ⟦ return ⟨Expression#1⟩ ; ⟧↑# ↑ok(And(#E1ok, Eq(#E1t, #rt))) ;

  // S → return ;

  // | S.ds = ε
  ⟦ return ; ⟧ ↑ds(NoNTs) ;

  // | S.ok = Eq(E.te, void, S.rt)
  Stert(⟦ return ; ⟧↑#) ↓te{:#te} ↓rt(#rt) → ⟦ return ; ⟧↑# ↑ok(Eq(⟦ void ⟧, #rt) ↓te{:#te}) ;

  ////////////////////////////////////////////////////////////////////////
  // IT (IfTail)

  sort IfTail | scheme ITtert(IfTail) ↓te ↓rt | ↑ok ;

  // IT → S1 else S2

  // | S1.te = S2.te = S.te
  // | S1.rt = S2.rt = S.rt
  ITtert(⟦ ⟨Statement#1⟩ else ⟨Statement#2⟩ ⟧↑#) ↓te{:#te} ↓rt(#rt)
    → ⟦ ⟨Statement Stert(#1) ↓te{:#te} ↓rt(#rt)⟩ else ⟨Statement Stert(#2) ↓te{:#te} ↓rt(#rt)⟩ ⟧↑# ;

  // | S.ok = S1.ok ∧ S2.ok
  ⟦ ⟨Statement#1 ↑ok(#S1ok)⟩ else ⟨Statement#2 ↑ok(#S2ok)⟩ ⟧ ↑ok(And(#S1ok, #S2ok)) ;
  
  // IT → S1

  // | S1.te = S.te
  // | S1.rt = S.rt
  ITtert(⟦ ⟨Statement#1⟩ ⟧↑#) → ⟦ ⟨Statement Stert(#1)⟩ ⟧↑# ;

  // | S.ok = S1.ok
  ⟦ ⟨Statement#1 ↑ok(#S1ok)⟩ ⟧ ↑ok(#S1ok) ;

  ////////////////////////////////////////////////////////////////////////
  // E (Expression)

  sort Expression | scheme Ete(Expression) ↓te | ↑t | ↑ok ;
  | scheme Ete2(Expression) ↓te ; // helper for several cases

  // Simple E.
  
  // E → id1
  // | E.t = Lookup(E.te, id1.sym)
  // | E.ok = Defined(E.te, id1.sym)
  Ete(⟦ ⟨IDENTIFIER#1⟩ ⟧↑#) ↓te{#1 : #1t} → ⟦ ⟨IDENTIFIER#1⟩ ⟧↑# ↑t(#1t) ↑ok(True) ;
  Ete(⟦ ⟨IDENTIFIER#1⟩ ⟧↑#) ↓te{¬#1} → ⟦ ⟨IDENTIFIER#1⟩ ⟧↑# ↑t(⟦void⟧) ↑ok(False) ;

  // E → str1
  Ete(⟦ ⟨STRING#1⟩ ⟧↑#) → ⟦ ⟨STRING#1⟩ ⟧↑# ; // dummy
  // | E.t = string
  ⟦ ⟨STRING#1⟩ ⟧ ↑t(⟦ string ⟧) ;
  // | E.ok = True
  ⟦ ⟨STRING#1⟩ ⟧ ↑ok(True) ;

  // E → int1
  Ete(⟦ ⟨INTEGER#1⟩ ⟧↑#) → ⟦ ⟨INTEGER#1⟩ ⟧↑# ; // dummy
  // | E.t = number
  ⟦ ⟨INTEGER#1⟩ ⟧ ↑t(⟦ number ⟧) ;
  // | E.ok = True
  ⟦ ⟨INTEGER#1⟩ ⟧ ↑ok(True) ;

  // Composite E.
  
  // E → E1 . id2
  // | E1.te = E.te
  // | E.t = MemberType(E.te, E1.t, id2.sym)
  // | E.ok = E1.ok ∧ IsMember(E.te, E1.t, id2.sym)
  Ete(⟦ ⟨Expression#1⟩ . ⟨IDENTIFIER#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ . ⟨IDENTIFIER#2⟩ ⟧↑#) ;
  // Once E1 is fully processed we can proceed.
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ . ⟨IDENTIFIER#2⟩ ⟧↑#)
    → ⟦ ⟨Expression Ete(#1)⟩ . ⟨IDENTIFIER#2⟩ ⟧↑#
    ↑t(LookupNTs(MemberMap(Resolve(#E1t)), #2))
    ↑ok(And(#E1ok, ContainsNs(KeysNTs(MemberMap(Resolve(#E1t))), #2))) ;

  // E → E1 ( EL2 )
  // | E1.te = EL2.te = E.te
  // | E.ok = E1.ok ∧ EL2.ok ∧ IsArguments(E.te, E1.t, EL2.ts)
  Ete(⟦ ⟨Expression#1⟩ ( ⟨ExpressionList#2⟩ ) ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ ( ⟨ExpressionList ELte(#2)⟩ ) ⟧↑#) ;
  // After all subterms are processed we can proceed.
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ ( ⟨ExpressionList#2 ↑ts(#EL2ts) ↑ok(#EL2ok)⟩ ) ⟧↑#)
    → ⟦ ⟨Expression#1⟩ ( ⟨ExpressionList#2⟩ ) ⟧↑#
    ↑ok(And(And(#E1ok, #EL2ok), EqTs(ArgumentTypes(#E1t), #EL2ts))) ;
  // | E.t = ReturnType(E1.t)
  ⟦ ⟨Expression#1 ↑t(#E1t)⟩ ( ⟨ExpressionList#2⟩ ) ⟧ ↑t(ReturnType(#E1t)) ;

  // Unary E.
  
  // E → ! E1
  // | E1.te = E.te
  // | E.ok = E1.ok ∧ Eq(E.te, boolean, E1.t)
  Ete(⟦ ! ⟨Expression#1⟩ ⟧↑#) → Ete2(⟦ ! ⟨Expression Ete(#1)⟩ ⟧↑#) ;
  Ete2(⟦ ! ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ ⟧↑#) → ⟦ ! ⟨Expression#1⟩ ⟧↑# ↑ok(And(#E1ok, Eq(⟦boolean⟧, #E1t))) ;
  // | E.t = boolean
  ⟦ ! ⟨Expression#1⟩ ⟧ ↑t(⟦ boolean ⟧) ;

  // E → ~ E1
  // | E1.te = E.te
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t)
  Ete(⟦ ~ ⟨Expression#1⟩ ⟧↑#) → Ete2(⟦ ~ ⟨Expression Ete(#1)⟩ ⟧↑#) ;
  Ete2(⟦ ~ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ ⟧↑#) → ⟦ ~ ⟨Expression#1⟩ ⟧↑# ↑ok(And(#E1ok, Eq(⟦number⟧, #E1t))) ;
  // | E.t = number
  ⟦ ~ ⟨Expression#1⟩ ⟧ ↑t(⟦ number ⟧) ;

  // E → - E1
  // | E1.te = E.te
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t)
  Ete(⟦ - ⟨Expression#1⟩ ⟧↑#) → Ete2(⟦ - ⟨Expression Ete(#1)⟩ ⟧↑#) ;
  Ete2(⟦ - ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ ⟧↑#) → ⟦ - ⟨Expression#1⟩ ⟧↑# ↑ok(And(#E1ok, Eq(⟦number⟧, #E1t))) ;
  // | E.t = number
  ⟦ - ⟨Expression#1⟩ ⟧ ↑t(⟦ number ⟧) ;

  // E → + E1
  // | E1.te = E.te
  // | E.ok = E1.ok ∧ Eq(E.te, number, E1.t)
  Ete(⟦ + ⟨Expression#1⟩ ⟧↑#) → Ete2(⟦ + ⟨Expression Ete(#1)⟩ ⟧↑#) ;
  Ete2(⟦ + ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ ⟧↑#) → ⟦ + ⟨Expression#1⟩ ⟧↑# ↑ok(And(#E1ok, Eq(⟦number⟧, #E1t))) ;
  // | E.t = number
  ⟦ + ⟨Expression#1⟩ ⟧ ↑t(⟦ number ⟧) ;

  // Binary E.

  // E → E1 * E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t)
  Ete(⟦ ⟨Expression#1⟩ * ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ * ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ * ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ * ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(⟦number⟧, #E1t), Eq(⟦number⟧, #E2t)))) ;
  // | E.t = number
  ⟦ ⟨Expression#1⟩ * ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 / E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t)
  Ete(⟦ ⟨Expression#1⟩ / ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ / ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ / ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ / ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(⟦number⟧, #E1t), Eq(⟦number⟧, #E2t)))) ;
  // | E.t = number
  ⟦ ⟨Expression#1⟩ / ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 % E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t)
  Ete(⟦ ⟨Expression#1⟩ % ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ % ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ % ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ % ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(⟦number⟧, #E1t), Eq(⟦number⟧, #E2t)))) ;
  // | E.t = number
  ⟦ ⟨Expression#1⟩ % ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 + E2

  // | E1.te = E2.te = E.te
  // | E.t = if Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t) then number else string
  // | E.ok = E1.ok ∧ E2.ok
  //     ∧ ( Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t) )
  //     ∧ ( Eq(E.te, number, E2.t) ∨ Eq(E.te, string, E2.t) )
  Ete(⟦ ⟨Expression#1⟩ + ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ + ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ + ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ + ⟨Expression#2⟩ ⟧↑#
    ↑t(NumberOrString(#E1t, #E2t))
    ↑ok(And(And(#E1ok, #E2ok),
	    And(Or(Eq(⟦number⟧, #E1t), Eq(⟦string⟧, #E1t)), Or(Eq(⟦number⟧, #E2t), Eq(⟦string⟧, #E2t))))) ;
  sort Type | scheme NumberOrString(Type, Type) ;
  NumberOrString(⟦number⟧, ⟦number⟧) → ⟦number⟧ ;
  default NumberOrString(#1, #2) → ⟦string⟧ ;
  sort Expression ;
  
  // E → E1 - E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t)
  Ete(⟦ ⟨Expression#1⟩ - ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ - ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ - ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ - ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(⟦number⟧, #E1t), Eq(⟦number⟧, #E2t)))) ;
  // | E.t = number
  ⟦ ⟨Expression#1⟩ - ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 & E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t)
  Ete(⟦ ⟨Expression#1⟩ & ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ & ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ & ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ & ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(⟦number⟧, #E1t), Eq(⟦number⟧, #E2t)))) ;
  // | E.t = number
  ⟦ ⟨Expression#1⟩ & ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 ^ E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t)
  Ete(⟦ ⟨Expression#1⟩ ^ ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ ^ ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ ^ ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ ^ ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(⟦number⟧, #E1t), Eq(⟦number⟧, #E2t)))) ;
  // | E.t = number
  ⟦ ⟨Expression#1⟩ ^ ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // E → E1 | E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t)
  Ete(⟦ ⟨Expression#1⟩ | ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ | ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ | ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ | ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(⟦number⟧, #E1t), Eq(⟦number⟧, #E2t)))) ;
  // | E.t = number
  ⟦ ⟨Expression#1⟩ | ⟨Expression#2⟩ ⟧ ↑t(⟦number⟧) ;

  // Inequality E
  
  // E → E1 <= E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete(⟦ ⟨Expression#1⟩ <= ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ <= ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ <= ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ <= ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(#E1t, #E2t), Or(Eq(⟦number⟧, #E1t), Eq(⟦string⟧, #E1t))))) ;
  // | E.t = boolean
  ⟦ ⟨Expression#1⟩ <= ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;
  
  // E → E1 >= E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete(⟦ ⟨Expression#1⟩ >= ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ >= ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ >= ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ >= ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(#E1t, #E2t), Or(Eq(⟦number⟧, #E1t), Eq(⟦string⟧, #E1t))))) ;
  // | E.t = boolean
  ⟦ ⟨Expression#1⟩ >= ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E → E1 < E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete(⟦ ⟨Expression#1⟩ < ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ < ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ < ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ < ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(#E1t, #E2t), Or(Eq(⟦number⟧, #E1t), Eq(⟦string⟧, #E1t))))) ;
  // | E.t = boolean
  ⟦ ⟨Expression#1⟩ < ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E → E1 > E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t) ∧ (Eq(E.te, number, E1.t) ∨ Eq(E.te, string, E1.t))
  Ete(⟦ ⟨Expression#1⟩ > ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ > ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ > ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ > ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(#E1t, #E2t), Or(Eq(⟦number⟧, #E1t), Eq(⟦string⟧, #E1t))))) ;
  // | E.t = boolean
  ⟦ ⟨Expression#1⟩ > ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // Equality E

  // E → E1 == E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t)
  Ete(⟦ ⟨Expression#1⟩ == ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ == ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ == ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ == ⟨Expression#2⟩ ⟧↑# ↑ok(And(And(#E1ok, #E2ok), Eq(#E1t, #E2t))) ;
  // | E.t = boolean
  ⟦ ⟨Expression#1⟩ == ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E → E1 != E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, E2.t, E1.t)
  Ete(⟦ ⟨Expression#1⟩ != ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ != ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ != ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ != ⟨Expression#2⟩ ⟧↑# ↑ok(And(And(#E1ok, #E2ok), Eq(#E1t, #E2t))) ;
  // | E.t = boolean
  ⟦ ⟨Expression#1⟩ != ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;
  
  // Logical E

  // E → E1 && E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, boolean, E1.t) ∧ Eq(E.te, boolean, E2.t)
  Ete(⟦ ⟨Expression#1⟩ && ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ && ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ && ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ && ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(⟦boolean⟧, #E1t), Eq(⟦boolean⟧, #E2t)))) ;
  // | E.t = boolean
  ⟦ ⟨Expression#1⟩ && ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // E → E1 || E2
  // | E1.te = E2.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ Eq(E.te, boolean, E1.t) ∧ Eq(E.te, boolean, E2.t)
  Ete(⟦ ⟨Expression#1⟩ || ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ || ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ || ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ || ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(And(#E1ok, #E2ok), And(Eq(⟦boolean⟧, #E1t), Eq(⟦boolean⟧, #E2t)))) ;
  // | E.t = boolean
  ⟦ ⟨Expression#1⟩ || ⟨Expression#2⟩ ⟧ ↑t(⟦boolean⟧) ;

  // Ternary E

  // E → E1 ? E2 : E3

  // | E1.te = E2.te = E3.te = E.te
  // | E.ok = E1.ok ∧ E2.ok ∧ E3.ok ∧ Eq(E.te, boolean, E1.t) ∧ Eq(E.te, E2.t, E3.t)
  Ete(⟦ ⟨Expression#1⟩ ? ⟨Expression#2⟩ : ⟨Expression#3⟩ ⟧↑#)
    → Ete2(⟦ ⟨Expression Ete(#1)⟩ ? ⟨Expression Ete(#2)⟩ : ⟨Expression Ete(#3)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ ? ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ : ⟨Expression#3 ↑t(#E3t) ↑ok(#E3ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ ? ⟨Expression#2⟩ : ⟨Expression#3⟩ ⟧↑#
    ↑ok(And(And(#E1ok, And(#E2ok, #E3ok)), And(Eq(⟦boolean⟧, #E1t), Eq(#E2t, #E3t)))) ;
  // | E.t = E2.t
  ⟦ ⟨Expression#1⟩ ? ⟨Expression#2 ↑t(#E2t)⟩ : ⟨Expression#3⟩ ⟧ ↑t(#E2t) ;

  // Asignment E

  // E → E1 = E2
  // | E1.te = E2.te = E.te
  // | E.ok = IsLValue(E1) ∧ E1.ok ∧ E2.ok ∧ Eq(E.te, E1.t, E2.t)
  Ete(⟦ ⟨Expression#1⟩ = ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ = ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ = ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ = ⟨Expression#2⟩ ⟧↑# ↑ok(And(IsLValue(#1), And(And(#E1ok, #E2ok), Eq(#E1t, #E2t)))) ;
  // | E.t = E1.t
  ⟦ ⟨Expression#1 ↑t(#E1t)⟩ = ⟨Expression#2⟩ ⟧ ↑t(#E1t) ;

  // E → E1 += E2
  // | E1.te = E2.te = E.te
  // | E.ok = IsLValue(E1) ∧ E1.ok ∧ E2.ok ∧ (
  //  			(Eq(E.te, number, E1.t) ∧ Eq(E.te, number, E2.t))
  //  			∨ (Eq(E.te, string, E1.t) ∧ (Eq(E.te, number, E2.t) ∨ Eq(E.te, string, E2.t)))
  //       )
  Ete(⟦ ⟨Expression#1⟩ += ⟨Expression#2⟩ ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ += ⟨Expression Ete(#2)⟩ ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t) ↑ok(#E1ok)⟩ += ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#)
    → ⟦ ⟨Expression#1⟩ += ⟨Expression#2⟩ ⟧↑#
    ↑ok(And(
	    And(IsLValue(#1), And(#E1ok, #E2ok)),
	    Or(And(Eq(⟦number⟧, #E1t), Eq(⟦number⟧, #E2t)),
	       And(Eq(⟦string⟧, #E1t), Or(Eq(⟦number⟧, #E2t), Eq(⟦string⟧, #E2t))) ))) ;
  // | E.t = E1.t
  ⟦ ⟨Expression#1 ↑t(#E1t)⟩ += ⟨Expression#2⟩ ⟧ ↑t(#E1t) ;

  // E → E1 = { KVL2 }
  // | E1.te = KVL2.te = E.te
  // | KVL2.r = MemberMap(E1.t)
  // | KVL2.ums = ε

  Ete(⟦ ⟨Expression#1⟩ = { ⟨KeyValueList#2⟩ } ⟧↑#) → Ete2(⟦ ⟨Expression Ete(#1)⟩ = { ⟨KeyValueList#2⟩ } ⟧↑#) ;
  Ete2(⟦ ⟨Expression#1 ↑t(#E1t)⟩ = { ⟨KeyValueList#2⟩ } ⟧↑#) ↓te{:#te}
  → ⟦ ⟨Expression#1⟩ = { ⟨KeyValueList KVLterumsExtend(#2, MemberMap(Resolve(#E1t)↓te{:#te})) ↓te{:#te} ↓ums(NoNs)⟩ } ⟧↑# ;
  
  // | E.t = E1.t
  ⟦ ⟨Expression#1 ↑t(#E1t)⟩ = { ⟨KeyValueList#2⟩ } ⟧ ↑t(#E1t) ;

  // | E.ok = IsLValue(E1) ∧ E1.ok ∧ KVL2.ok
  ⟦ ⟨Expression#1 ↑ok(#E1ok)⟩ = { ⟨KeyValueList#2 ↑ok(#KVL2ok)⟩ } ⟧
    ↑ok(And(IsLValue(#1), And(#E1ok, #KVL2ok))) ;

  ////////////////////////////////////////////////////////////////////////
  // EL (ExpressionList)

  sort ExpressionList | scheme ELte(ExpressionList) ↓te | ↑ts | ↑ok ;

  // EL → E1 ELT2

  // | E1.te = ELT2 .te = EL.te
  ELte(⟦ ⟨Expression#1⟩ ⟨ExpressionListTail#2⟩ ⟧↑#) → ⟦ ⟨Expression Ete(#1)⟩ ⟨ExpressionListTail ELTte(#2)⟩ ⟧↑# ;

  // | EL.ts = (E1.t) ∥ ELT2.ts
  ⟦ ⟨Expression#1 ↑t(#E1t)⟩ ⟨ExpressionListTail#2 ↑ts(#ELT2ts)⟩ ⟧ ↑ts(MoTs(#E1t, #ELT2ts)) ;

  // | EL.ok = E1.ok ∧ ELT2.ok
  ⟦ ⟨Expression#1 ↑ok(#E1ok)⟩ ⟨ExpressionListTail#2 ↑ok(#ELT2ok)⟩ ⟧ ↑ok(And(#E1ok, #ELT2ok)) ;

  // EL → ε
  ELte(⟦ ⟧↑#) → ⟦ ⟧↑# ; // dummy

  // | EL.ts = ε
  ⟦ ⟧ ↑ts(NoTs) ;
  
  // | EL.ok = True
  ⟦ ⟧ ↑ok(True) ;

  ////////////////////////////////////////////////////////////////////////
  // ELT (ExpressionListTail)

  sort ExpressionListTail | scheme ELTte(ExpressionListTail) ↓te | ↑ts | ↑ok ;

  // ELT → , E1 ELT2

  // | E1.te = ELT2 .te = ELT.te
  ELTte(⟦ , ⟨Expression#1⟩ ⟨ExpressionListTail#2⟩ ⟧↑#) → ⟦ , ⟨Expression Ete(#1)⟩ ⟨ExpressionListTail ELTte(#2)⟩ ⟧↑# ;

  // | ELT.ts = (E1.t) ∥ ELT2.ts
  ⟦ , ⟨Expression#1 ↑t(#E1t)⟩ ⟨ExpressionListTail#2 ↑ts(#ELT2ts)⟩ ⟧ ↑ts(MoTs(#E1t, #ELT2ts)) ;

  // | ELT.ok = E1.ok ∧ ELT2.ok
  ⟦ , ⟨Expression#1 ↑ok(#E1ok)⟩ ⟨ExpressionListTail#2 ↑ok(#ELT2ok)⟩ ⟧ ↑ok(And(#E1ok, #ELT2ok)) ;

  // ELT → ε
  ELTte(⟦ ⟧↑#) → ⟦ ⟧↑# ; // dummy

  // | ELT.ts = ε
  ⟦ ⟧ ↑ts(NoTs) ;
  
  // | ELT.ok = True
  ⟦ ⟧ ↑ok(True) ;

  ////////////////////////////////////////////////////////////////////////
  // KVL (KeyValueList)

  sort KeyValueList | scheme KVLterums(KeyValueList) ↓te ↓r ↓ums | ↑ok ;

  // Cascade helper to initialize KVLterums map propagation below.
  | scheme KVLterumsExtend(Units, NTs) ↓te ↓r ↓ums;
  KVLterumsExtend(#1, NoNTs) ↓te{:#te} ↓r{:#r} ↓ums(#ums) → KVLterums(#1) ↓te{:#te} ↓r{:#r} ↓ums(#ums) ;
  KVLterumsExtend(#1, MoNTs(#ID, #T, #2)) ↓te{:#te} ↓r{:#r} ↓ums(#ums)
    → KVLterumsExtend(#1, #2) ↓te{:#te} ↓r{:#r} ↓ums(#ums) ↓r{#ID : #T};

  // KVL → KV1 KVLT2

  // | KV1.te = KVLT2.te = KVL.te
  // | KV1.r = KVLT2.r = KVL.r
  // | KVLT2.ums = KVL.ums ∥ KV1.id
  // | KVLT.ok = KV1.ok ∧ Key(KV1) ∉ KVL.ums ∧ KVLT2.ok
  KVLterums(⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧↑#) ↓te{:#te} ↓r{:#r} ↓ums(#ums)
    → KVLterums2(⟦ ⟨KeyValue KVter(#1)↓te{:#te}↓r{:#r}⟩ ⟨KeyValueListTail KVLTterums(#2) ↓te{:#te} ↓r{:#r} ↓ums(AddKey(#ums, #1))⟩ ⟧↑#) ↓ums(#ums);
  // we need a second pass to compute ok
  | scheme KVLterums2(KeyValueList) ↓ums ;
  KVLterums2(⟦ ⟨KeyValue#1 ↑ok(#KV1ok)⟩ ⟨KeyValueListTail#2 ↑ok(#KVLT2ok)⟩ ⟧↑#) ↓ums(#ums)
    → ⟦ ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧↑#
    ↑ok(And(And(#KV1ok, #KVLT2ok), Not(KeyIn(#ums, #1)))) ;

  // KVL → ε
  KVLterums(⟦ ⟧↑#) → ⟦ ⟧↑# ; // dummy
  
  // | KVL.ok = True
  ⟦ ⟧ ↑ok(True) ;

  ////////////////////////////////////////////////////////////////////////
  // KVLT (KeyValueListTail)

  sort KeyValueListTail | scheme KVLTterums(KeyValueListTail) ↓te ↓r ↓ums | ↑ok ;

  // KVLT → , KV1 KVLT2

  // | KV1.te = KVLT2.te = KVLT.te
  // | KV1.r = KVLT2.r = KVLT.r
  // | KVLT2.ums = KVLT.ums ∥ KV1.id
  // | KVLT.ok = KV1.ok ∧ Key(KV1) ∉ KVLT.ums ∧ KVLT2.ok
  KVLTterums(⟦ , ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧↑#) ↓te{:#te} ↓r{:#r} ↓ums(#ums)
    → KVLTterums2(⟦ , ⟨KeyValue KVter(#1)↓te{:#te} ↓r{:#r}⟩ ⟨KeyValueListTail KVLTterums(#2)↓te{:#te} ↓r{:#r} ↓ums(AddKey(#ums, #1))⟩ ⟧↑#);
  // we need a second pass to compute ok
  | scheme KVLTterums2(KeyValueListTail) ↓ums ;
  KVLTterums2(⟦ , ⟨KeyValue#1 ↑ok(#KV1ok)⟩ ⟨KeyValueListTail#2 ↑ok(#KVLT2ok)⟩ ⟧↑#) ↓ums(#ums)
    → ⟦ , ⟨KeyValue#1⟩ ⟨KeyValueListTail#2⟩ ⟧↑#
    ↑ok(And(And(#KV1ok, #KVLT2ok), Not(KeyIn(#ums, #1)))) ;

  // KVLT → ε
  KVLTterums(⟦ ⟧↑#) → ⟦ ⟧↑# ; // dummy
  
  // | KVLT.ok = True
  ⟦ ⟧ ↑ok(True) ;

  ////////////////////////////////////////////////////////////////////////
  // KV (KeyValue)

  sort KeyValue | scheme KVter(KeyValue) ↓te ↓r | ↑ok ;

  // KV → id1 : E2

  // | E2.te = KV.te
  // | KV.ok = E2.ok ∧ Eq(KV.te, Lookup(KV.r, id1.sym), E2.t)
  KVter(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧↑#)↓te{:#te} ↓r{:#r}  → KVter2(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression Ete(#2) ↓te{:#te}⟩ ⟧↑#) ↓te{:#te} ↓r{:#r}  ;
  | scheme KVter2(KeyValue) ↓te ↓r ;
  KVter2(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#) ↓te{:#te} ↓r{#1 : #1t}
  → ⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧↑# ↑ok(And(#E2ok, Eq(#1t, #E2t) ↓te{:#te})) ;
  KVter2(⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2 ↑t(#E2t) ↑ok(#E2ok)⟩ ⟧↑#) ↓te{:#te} ↓r{¬#1}
  → ⟦ ⟨IDENTIFIER#1⟩ : ⟨Expression#2⟩ ⟧↑# ↑ok(False) ;

  ////////////////////////////////////////////////////////////////////////
  // SEMANTIC OPERATIONS.

  sort NTs | scheme GlobalDefs ;
  GlobalDefs →
    MoNTs(⟦document⟧, ⟦ { body : {innerHTML : string } } ⟧,
    MoNTs(⟦length⟧, ⟦ (string) => number ⟧,
    MoNTs(⟦charAt⟧, ⟦ (string, number) => number ⟧,
    MoNTs(⟦substr⟧, ⟦ (string, number, number) => string ⟧,
    NoNTs)))) ;
  
  // Resolve: unpack interface names.
  sort Type | scheme Resolve(Type) ↓te | scheme Resolve2(Type) ↓te ;
  [data #] Resolve(#) ↓te{:#te} → Resolve2(#) ↓te{:#te} ;
  Resolve2(⟦ ⟨IDENTIFIER#1⟩ ⟧) ↓te{#1 : #1t} → #1t ;
  default Resolve2(#) → # ;

  // Eq, EqTs, EqNTs: structural type equality, with resolution from te as needed.
  sort Bool | scheme Eq(Type, Type) ↓te ;
  [data #1, data #2] Eq(#1, #2) → Eq0(#1, #2) ;

  sort Bool | scheme Eq0(Type, Type) ↓te ; // resolve if needed
  Eq0(⟦ ⟨IDENTIFIER#1⟩ ⟧, ⟦ ⟨IDENTIFIER#1⟩ ⟧) → True ;
  Eq0(⟦ ⟨IDENTIFIER#1⟩ ⟧, ⟦ { ⟨NameTypeList#2⟩ } ⟧) → Eq1(Resolve(⟦ ⟨IDENTIFIER#1⟩ ⟧), ⟦ { ⟨NameTypeList#2⟩ } ⟧) ;
  Eq0(⟦ { ⟨NameTypeList#1⟩ } ⟧, ⟦ ⟨IDENTIFIER#2⟩ ⟧) → Eq1(⟦ { ⟨NameTypeList#1⟩ } ⟧, Resolve(⟦ ⟨IDENTIFIER#2⟩ ⟧)) ;
  default Eq0(#1, #2) → Eq1(#1, #2) ;

  sort Bool | scheme Eq1(Type, Type) ↓te ; // force resolution
  [data #1, data #2] Eq1(#1, #2) → Eq2(#1, #2) ;

  sort Bool | scheme Eq2(Type, Type) ↓te ; // compare resolved types
  Eq2(⟦boolean⟧, ⟦boolean⟧) → True ;
  Eq2(⟦number⟧, ⟦number⟧) → True ;
  Eq2(⟦string⟧, ⟦string⟧) → True ;
  Eq2(⟦void⟧, ⟦void⟧) → True ;
  Eq2(⟦ ( ⟨TypeList#11⟩ ) => ⟨Type#12⟩ ⟧, ⟦ ( ⟨TypeList#21⟩ ) => ⟨Type#22⟩ ⟧)
    → And(EqTs(TypeListTypes(#11), TypeListTypes(#21)), Eq(#12, #22)) ;
  Eq2(⟦ { ⟨NameTypeList#1⟩ } ⟧, ⟦ { ⟨NameTypeList#2⟩ } ⟧)
    → EqNTs(NameTypeListMap(#1), NameTypeListMap(#2)) ;
  default Eq2(#1, #2) → False ;
  
  sort Bool | scheme EqTs(Ts, Ts) ↓te ; // identical type lists?
  [data #1, data #2] EqTs(#1, #2) → EqTs0(#1, #2) ;
  sort Bool | scheme EqTs0(Ts, Ts) ↓te ; // identical type lists
  EqTs0(MoTs(#T1, #1), MoTs(#T2, #2)) → And(Eq(#T1, #T2), EqTs(#1, #2)) ;
  EqTs0(NoTs, NoTs) → True ;
  default EqTs0(#1, #2) → False ;

  sort Bool | scheme EqNTs(NTs, NTs) ↓te ; // identical name-type pairs, modulo order
  [data #1, data #2] EqNTs(#1, #2) → And(EqNTs1(#1, #2, True), EqNTs1(#2, #1, False)) ;
  attribute ↓nts1{IDENTIFIER : Type} ;
  sort Bool | scheme EqNTs1(NTs, NTs, Bool) ↓te ↓nts1; // collect left mappings in ↓nts1 and then...
  EqNTs1(MoNTs(#ID1, #T1, #1), #2, #test) → EqNTs1(#1, #2, #test) ↓nts1{#ID1 : #T1} ;
  EqNTs1(NoNTs, #2, #test) → EqNTs2(#2, #test) ;
  sort Bool | scheme EqNTs2(NTs, Bool) ↓te ↓nts1; // ...check all right mappings exist in ↓nts1 (optionally with same type)
  EqNTs2(MoNTs(#ID, #T, #), #test) ↓nts1{¬#ID} → False ;
  EqNTs2(MoNTs(#ID, #T, #), False) ↓nts1{#ID : #T2} → EqNTs2(#, False) ;
  EqNTs2(MoNTs(#ID, #T, #), True) ↓nts1{#ID : #T2} → And(Eq(#T, #T2), EqNTs2(#, True)) ;
  EqNTs2(NoNTs, #test) → True ;

  ////////////////////////////////////////////////////////////////////////
  // 6. SUBSCRIPT TO MINARM32 COMPILER
  ////////////////////////////////////////////////////////////////////////

  // Implements compiler from SubScript to MinARM32.

  // Called from entry point.
  sort ARM | scheme CP(Program);
  CP(#P) → ⟦ main: MOV PC,LR /* Replace with your compiler! */ ⟧ ;

  // TODO: Implement the full translation from SubScript to MinARM32.
    
}
