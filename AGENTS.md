# trashlean contribution policy

- Use Mathlib and mathematically substantive techniques.
- Explicitly distinguish fictional modeling assumptions from real-world claims.
- Prove auxiliary results and a headline theorem; avoid sorry, admit, and new axioms.
- Keep a module in Trashlean/ for each theorem and register it in Trashlean.lean.
- Maintain the theorem index in README.md.
- Run lake build and inspect #print axioms for headline theorems.
- Do not claim successful verification unless the Lean kernel actually checked the file.
