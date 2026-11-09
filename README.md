# Ehrhart volume inequality: attempts by a distilled 4B student

Raw reasoning traces from a Spark-X2.6-4B student (LoRA distilled from 8 teacher reasoning traces on a Lean file about Connes rigidity) asked to attack `ehrhart_volume_inequality_for_sets`: a convex body with centroid 0 and 0 as its only interior lattice point has volume at most (n+1)^n / n!.

**Result: no proof was produced.** No attempt closed its thinking block; every run ended on the token limit (run 1) or was stopped by hand (run 2). The traces repeat several wrong ideas (induction on slices, polar body, difference body) and contain made-up citations. They are published as raw data, not as mathematics to rely on.

| Files | Run | Setup |
|---|---|---|
| `run1_connes_lora_32k_attempt_0..7.json` | 1 | Connes-LoRA, 8 attempts, 32,768 tokens each |
| `run2_oldlora_think_attempt_0..3.json` | 2 | older LoRA continued on the same 8 teachers with thinking, 4 attempts, stopped at about 59k of 79,488 tokens |
| `prompt.txt` | | the prompt given to the student |
| `run1_log.txt`, `run2_log.txt` | | generation logs |

Each JSON has `text` (the full reasoning), `ntok`, `finished`. Some characters in `text` are mojibake from the terminal capture.

The theorem itself was reported as proved by OpenAI (Aug 2026, Lean certificates, not peer reviewed); nothing here is related to that proof.
