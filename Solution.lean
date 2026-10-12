module

public import ESCtoFroberg.Main

@[expose] public section

namespace ESCtoFrobergPaper

/-- Theorem 1.1, in the independent actual-ring statement. -/
theorem main_result : ESCtoFroberg.Independent.Theorem11 :=
  ESCtoFroberg.independent_main_result

end ESCtoFrobergPaper
