# Formalization requirements

Read the README and the selected target's source snapshot, guide and evidence.
Keep the pinned Lean/mathlib pair and use mathlib definitions and theorems
where possible. No `sorry`, `admit` or unreported axioms are acceptable.

Verify the written argument, not only a theorem with the same conclusion.
Retain exact statement and proof revisions, and map each substantive step to
Lean with matching hypotheses and dependencies. Repair differences in Lean
where possible. A different checked proof does not verify the original argument.

Math Research's internal research notes are the mathematical source; its wiki
is their exposition. Record necessary alternative arguments in internal proof
notes with enough detail to reproduce them, preserving the original argument.
The Lean role does not edit the wiki to match its code. Mathematical
reconciliation and subsequent exposition are separate tasks. Follow the parent
project's mailbox and path-ownership rules when working in that project.

Keep explicit unproved inputs and unfinished local bridges visible. An axiom
audit does not discharge theorem parameters or establish proof correspondence.
Run the local verification and statement checks, retain actual output and input
hashes, and distinguish author self-checks from independent review. Do not
introduce visitor approval controls or human-gated verification.

When the written proof invokes a standard theorem, invoke the corresponding
named theorem in Lean. If it is missing from mathlib, keep its proof in a
separate background module with its own exact statement and evidence. If that
proof is not available, expose the theorem as an explicit hypothesis and label
the research result conditional. Never insert a replacement background proof
inside the research argument merely to obtain an unconditional result. Audit
previous work for this boundary and maintain an internal list for separate
expository articles. Do not expand the scope of a verification label beyond
the actual specialized declaration.
