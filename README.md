# Project S · P05 · Four-pass Shellsort reachability

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

The available Lean results give lower bounds for actual execution from slot potentials and the capacity of a single checkpoint. The specific four-pass separation for (m,4,2,1) and its final-pass asymptotic are still awaiting a dedicated Lean proof.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

Additional executable check: after the build, run `lake env lean FourSlotExample.lean`. See [FourSlotExample.lean](FourSlotExample.lean).

## Proof guide

[Read the proof idea in Chinese](brief.md). The guide explains the mathematical claim and the scope of the Lean results linked above.
