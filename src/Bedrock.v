Require Export PropX PropXTac Machine Assembly Structured Separation.

Require Export String List TheoryList.

Notation "st ~> P" := (fun st => P%PropX%nat) (at level 100, only parsing).
