open Name
open Types


let types = [(TName "->", KArrow (KStar, KArrow (KStar, KStar)));
     (TName "int", KStar);
     (TName "char", KStar);
     (TName "unit", KStar)]


