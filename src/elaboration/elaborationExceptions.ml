open Positions
open Name

exception UnboundIdentifier of position * name
exception UnboundTypeVariable of position * tname
exception UnboundClass of position * cname
exception UnboundLabel of position * lname
exception MultipleLabels of position * lname
exception AlreadyDefinedClass of position * cname
exception InvalidTypeApplication of position
exception InvalidDataConstructorApplication of position
exception PatternsMustBindSameVariables of position
exception CannotElaborateDictionary of position * Types.t
exception UnboundIdentifier of position * name
exception NonLinearPattern of position
exception IncompatibleTypes of position * Types.t * Types.t
exception IncompatibleKinds of position * Types.kind * Types.kind
exception IllKindedType of position
exception RecordExpected of position * Types.t
exception ApplicationToNonFunctional of position
exception ValueRestriction of position
exception InvalidOverloading of position
exception OverloadingOfNonValueFormForbidden of position
exception InvalidNumberOfTypeAbstraction of position
exception TheseTwoClassesMustNotBeInTheSameContext of position * cname * cname
exception OverlappingInstances of position * cname
exception OnlyLetsCanIntroduceTypeAbstraction of position
exception SameNameInTypeAbstractionAndScheme of position
exception LabelAlreadyTaken of position * lname
exception LabelDoesNotBelong of position * lname * tname * tname
exception InvalidRecordInstantiation of position

exception OverloadedSymbolCannotBeBound of Positions.position * name
exception InvalidRecordConstruction of position

exception VariableIsAMethodName of position * name
exception AmbiguousTypeclass of position * cname
exception TooFreeTypeVariableTypeclass of position * cname
exception NotAMethodOf of position * lname * cname
exception MultipleMethods of position * lname
exception LackingMethod of position * cname * lname
exception TooManyMethods of position * cname
exception NotAnInstance of position * cname * Types.t
exception NotCanonicalConstraint of position

exception NotImplemented of position * string
