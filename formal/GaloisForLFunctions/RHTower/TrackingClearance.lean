/-
# TrackingClearance — doc 25 (E2) and Corollary C (task #143 / #135 substrate)

Doc 25 (25-tracking-clearance.md) `[PROVED HERE]` pieces not already banked elsewhere
(Lemma W is `SpurHermite.hermite_equilibrium_energy`; (E4)/(E5) live in `JensenSection`/
`SpurRescale`). Flat grading: completing-the-square algebra; nothing new.

* `qRescaled_eq` — **(E2)**: the rescaled pair-quadratic `q_d(z/d) = |τ|² − 2az + (1−1/d)z²`
  completes to `(z − a)² + b² − z²/d`.
* `qRescaled_lower` — on `|z| ≤ R`, `q_d(z/d) ≥ b² − R²/d`.
* `qRescaled_ge_half` — `q_d(z/d) ≥ b²/2` once `d ≥ 2R²/b²` (the (E2) working bound feeding
  Theorem A).
* `qOrig_factor` — **Corollary C**: `q_d(c) = (b² − a²/(d−1)) + d(d−1)(c − a/(d−1))²`, so
  `q_d` is minimized at the dip `c = a/(d−1)` with value `b² − a²/(d−1)`.
* `qOrig_min_at` / `qOrig_ge_min` — the dip value and the global lower bound: the `q_d`-dip
  lies inside the tracking window, subsuming part (ii) of (AMP-mono) into part (i).
-/
import Mathlib

noncomputable section

namespace RHTower

/-- The rescaled pair-quadratic `q_d(z/d) = |τ|² − 2az + (1 − 1/d)z²`, `τ = a + bi`,
`|τ|² = a² + b²` (doc 25 §1 (E2)). -/
def qRescaled (a b : ℝ) (d : ℕ) (z : ℝ) : ℝ :=
  (a ^ (2 : ℕ) + b ^ (2 : ℕ)) - 2 * a * z + (1 - 1 / (d : ℝ)) * z ^ (2 : ℕ)

/-- The original pair-quadratic `q_d(c) = |τ|² − 2adc + d(d−1)c²` (doc 25 §0). -/
def qOrig (a b : ℝ) (d : ℕ) (c : ℝ) : ℝ :=
  (a ^ (2 : ℕ) + b ^ (2 : ℕ)) - 2 * a * (d : ℝ) * c + (d : ℝ) * ((d : ℝ) - 1) * c ^ (2 : ℕ)

/-- **(E2) completed square**: `q_d(z/d) = (z − a)² + b² − z²/d` (doc 25 §1). -/
theorem qRescaled_eq {a b : ℝ} {d : ℕ} (hd : 0 < d) (z : ℝ) :
    qRescaled a b d z = (z - a) ^ (2 : ℕ) + b ^ (2 : ℕ) - z ^ (2 : ℕ) / (d : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  unfold qRescaled
  field_simp
  ring

/-- **(E2) lower bound on the window**: `q_d(z/d) ≥ b² − R²/d` for `|z| ≤ R` (doc 25 §1). -/
theorem qRescaled_lower {a b R z : ℝ} {d : ℕ} (hd : 0 < d) (hz : |z| ≤ R) :
    b ^ (2 : ℕ) - R ^ (2 : ℕ) / (d : ℝ) ≤ qRescaled a b d z := by
  have hd0 : (0 : ℝ) < d := by positivity
  rw [qRescaled_eq hd]
  have hab := abs_le.mp hz
  have hzR : z ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := sq_le_sq' hab.1 hab.2
  have h1 : z ^ (2 : ℕ) / (d : ℝ) ≤ R ^ (2 : ℕ) / (d : ℝ) := by gcongr
  linarith [sq_nonneg (z - a), h1]

/-- **(E2) working bound**: `q_d(z/d) ≥ b²/2` once `d ≥ 2R²/b²`, i.e. `2R² ≤ b²d`
(doc 25 §1 — the definiteness threshold feeding Theorem A). -/
theorem qRescaled_ge_half {a b R z : ℝ} {d : ℕ} (hd : 0 < d) (hz : |z| ≤ R)
    (hthr : 2 * R ^ (2 : ℕ) ≤ b ^ (2 : ℕ) * (d : ℝ)) :
    b ^ (2 : ℕ) / 2 ≤ qRescaled a b d z := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hlow := qRescaled_lower (a := a) (b := b) hd hz
  have hRd : R ^ (2 : ℕ) / (d : ℝ) ≤ b ^ (2 : ℕ) / 2 := by
    rw [div_le_div_iff₀ hd0 (by norm_num)]
    linarith
  linarith

/-- **Corollary C — the dip factorization**: `q_d(c) = (b² − a²/(d−1)) + d(d−1)(c − a/(d−1))²`
(doc 25 §4). Hence `q_d` is minimized at `c = a/(d−1)`. -/
theorem qOrig_factor {a b : ℝ} {d : ℕ} (hd : 1 < d) (c : ℝ) :
    qOrig a b d c
      = (b ^ (2 : ℕ) - a ^ (2 : ℕ) / ((d : ℝ) - 1))
        + (d : ℝ) * ((d : ℝ) - 1) * (c - a / ((d : ℝ) - 1)) ^ (2 : ℕ) := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℝ) - 1 ≠ 0 := by linarith
  unfold qOrig
  field_simp
  ring

/-- **Corollary C — the dip value**: `q_d(a/(d−1)) = b² − a²/(d−1)` (doc 25 §4). -/
theorem qOrig_min_at {a b : ℝ} {d : ℕ} (hd : 1 < d) :
    qOrig a b d (a / ((d : ℝ) - 1)) = b ^ (2 : ℕ) - a ^ (2 : ℕ) / ((d : ℝ) - 1) := by
  rw [qOrig_factor hd]
  simp

/-- **Corollary C — global lower bound**: `q_d(c) ≥ b² − a²/(d−1)` for every `c`, with equality
at the dip `c = a/(d−1)` (doc 25 §4). The dip lies inside the tracking window, subsuming part
(ii) of (AMP-mono) into part (i). -/
theorem qOrig_ge_min {a b : ℝ} {d : ℕ} (hd : 1 < d) (c : ℝ) :
    b ^ (2 : ℕ) - a ^ (2 : ℕ) / ((d : ℝ) - 1) ≤ qOrig a b d c := by
  have hd1 : (1 : ℝ) < d := by exact_mod_cast hd
  rw [qOrig_factor hd]
  have : 0 ≤ (d : ℝ) * ((d : ℝ) - 1) * (c - a / ((d : ℝ) - 1)) ^ (2 : ℕ) := by positivity
  linarith

/-- **(E1) energy identity, critical-point form** (doc 25 §1): the second logarithmic
derivative `(A″A − A′²)/A²` collapses to `A″/A` at a critical point `A′ = 0`. Since the second
log-derivative is `−Σ(x−α_k)⁻²` for a hyperbolic `A`, this is `ℰ(c) = −A″(c)/A(c)` — the exact
datum that carries the whole far tail of `ℰ`, no spacing input needed. -/
theorem energy_at_crit {A dA d2A : ℝ} (hcrit : dA = 0) (hA : A ≠ 0) :
    (d2A * A - dA ^ (2 : ℕ)) / A ^ (2 : ℕ) = d2A / A := by
  subst hcrit
  field_simp
  ring

/-- **Theorem A — the clearance division** (doc 25 §2): once the (E3) uniform bounds hold —
`q_d(c) ≥ b²/2` (E2) and `c⁴ℰ(c) ≤ 2(M_R+1)R⁴/(m_ε d²)` (E1+E3) — the margin clears at rate
`d²`: `margin(c) = q_d(c)/(c⁴ℰ(c)) ≥ κ_A d²`, `κ_A = b²m_ε/(4(M_R+1)R⁴)`. The analytic inputs
enter only as the two hypotheses; the `d²`-clearance is then arithmetic. -/
theorem theoremA_margin_lower {q cE b mε MR R : ℝ} {d : ℕ}
    (hb : 0 < b) (hq : b ^ (2 : ℕ) / 2 ≤ q) (hcEpos : 0 < cE)
    (hmε : 0 < mε) (hMR : 0 ≤ MR) (hR : 0 < R) (hd : 0 < d)
    (hcE : cE ≤ 2 * (MR + 1) * R ^ (4 : ℕ) / (mε * (d : ℝ) ^ (2 : ℕ))) :
    b ^ (2 : ℕ) * mε * (d : ℝ) ^ (2 : ℕ) / (4 * (MR + 1) * R ^ (4 : ℕ)) ≤ q / cE := by
  have hd0 : (0 : ℝ) < d := by positivity
  have hB : (0 : ℝ) < 2 * (MR + 1) * R ^ (4 : ℕ) / (mε * (d : ℝ) ^ (2 : ℕ)) := by positivity
  have h2 : (b ^ (2 : ℕ) / 2) / (2 * (MR + 1) * R ^ (4 : ℕ) / (mε * (d : ℝ) ^ (2 : ℕ))) ≤ (b ^ (2 : ℕ) / 2) / cE := by
    gcongr
  have h3 : (b ^ (2 : ℕ) / 2) / cE ≤ q / cE := by gcongr
  have hkey : b ^ (2 : ℕ) * mε * (d : ℝ) ^ (2 : ℕ) / (4 * (MR + 1) * R ^ (4 : ℕ))
      = (b ^ (2 : ℕ) / 2) / (2 * (MR + 1) * R ^ (4 : ℕ) / (mε * (d : ℝ) ^ (2 : ℕ))) := by
    field_simp
    ring
  rw [hkey]
  linarith

end RHTower
