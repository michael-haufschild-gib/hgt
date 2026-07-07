/-
Conservation law for deck-charge motion on a box boundary.

The rung-`k` box charge `boxCharge k f c r` is the winding number of the carrier `f` around the circle
`∂B(c,r)`, reduced mod `2^k` — the loop realisation of the deck charge of that boundary.  Three laws
govern how it moves under deformation of `f`:

* **Interior conservation** (`boxCharge_conserved`): a continuous deformation `f_σ` that stays nonzero
  on `∂B` cannot change the charge — it is neither created nor destroyed in the interior.  (Homotopy
  invariance of the winding number.)
* **Boundary crossing** (`boxCharge_gain_zero`): when a zero of order `m'` enters the enclosed region
  (`f' = (·−ρ')^{m'}·f`), the charge jumps by exactly that zero's charge `w_k(m')`.  Charge changes
  only through the boundary.
* **Pair annihilation** (`pair_annihilation_iff`): the net charge of two enclosed defects vanishes —
  they can cancel through the boundary by a conserving deformation — exactly when their orders sum to a
  multiple of `2^k`, i.e. their charges are opposite.  At the base rung this is same-parity of the two
  orders (`pair_annihilation_level_one`).

The closing lemma `defect_not_removable` is the point of the phase: a defect of nontrivial charge
survives every boundary-nonvanishing deformation, so *conservation alone does not kill a defect* — a
parity/seam input (the fixed-point forcing of `SignedReflectionParity`) is what decides whether a
cancellation is legal.
-/
import GaloisForLFunctions.RHTower.WindingFull
import GaloisForLFunctions.RHTower.WindingHomotopy

open Complex Set

namespace RHTower

/-- The rung-`k` deck charge on the boundary circle `∂B(c,r)` of a carrier `f`: the winding number of
`f` around the circle, reduced mod `2^k`. -/
noncomputable def boxCharge (k : ℕ) (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ZMod (2 ^ k) :=
  loopCharge k (fun θ => f (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)

/-- **Interior conservation.**  Along a continuous deformation `f_σ` of carriers that stays nonzero on
the boundary circle `∂B(c,r)`, the box charge is constant: charge is neither created nor destroyed in
the interior — the homotopy invariance of the winding number, read as the deck charge. -/
theorem boxCharge_conserved (k : ℕ) {f : ℝ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hcont : Continuous (fun p : ℝ × ℝ => f p.1 (c + ↑r * exp (I * ↑p.2))))
    (hnv : ∀ σ θ : ℝ, f σ (c + ↑r * exp (I * ↑θ)) ≠ 0) :
    boxCharge k (f 0) c r = boxCharge k (f 1) c r := by
  have hloop : ∀ σ : ℝ, f σ (c + ↑r * exp (I * ↑(0 : ℝ)))
      = f σ (c + ↑r * exp (I * ↑(2 * Real.pi))) := by
    intro σ
    congr 2
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      show (I * ((2 * Real.pi : ℝ) : ℂ)) = (2 * (Real.pi : ℂ) * I) by push_cast; ring,
      Complex.exp_two_pi_mul_I]
  have hwind := windingNumber_of_homotopic (a := 0) (b := 2 * Real.pi)
    (fun σ θ => f σ (c + ↑r * exp (I * ↑θ))) hcont hnv hloop (fun _ => rfl) (fun _ => rfl)
  unfold boxCharge loopCharge
  rw [hwind]

/-- **Boundary-crossing formula (winding ledger jump).**  If the carrier gains one enclosed zero of
order `m'` at `ρ'` (`f' = (·−ρ')^{m'}·f` on the boundary circle, `ρ'` strictly inside, `f` continuous
and nonzero on the circle), the box charge jumps by exactly that zero's charge: `w_k(f') = w_k(f) +
w_k(m')`.  Charge changes only through the boundary, by the crossing zero's order. -/
theorem boxCharge_gain_zero (k : ℕ) {f f' : ℂ → ℂ} {c ρ' : ℂ} {r : ℝ} {m' : ℕ}
    (hr : 0 < r) (hin : ‖ρ' - c‖ < r)
    (hfc : Continuous (fun θ : ℝ => f (c + ↑r * exp (I * ↑θ))))
    (hfnv : ∀ θ : ℝ, f (c + ↑r * exp (I * ↑θ)) ≠ 0)
    (hfact' : ∀ θ : ℝ, f' (c + ↑r * exp (I * ↑θ))
      = ((c + ↑r * exp (I * ↑θ)) - ρ') ^ m' * f (c + ↑r * exp (I * ↑θ))) :
    boxCharge k f' c r = boxCharge k f c r + wCharge (2 ^ k) (m' : ℤ) := by
  have hLlin : IsLoop (fun θ => (c + ↑r * exp (I * ↑θ)) - ρ') 0 (2 * Real.pi) :=
    isLoop_linear_enclosing hr hin
  have hclosed : (c + ↑r * exp (I * ↑(0 : ℝ))) = (c + ↑r * exp (I * ↑(2 * Real.pi))) := by
    rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      show (I * ((2 * Real.pi : ℝ) : ℂ)) = (2 * (Real.pi : ℂ) * I) by push_cast; ring,
      Complex.exp_two_pi_mul_I]
  have hLf : IsLoop (fun θ => f (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi) :=
    ⟨hfc, hfnv, by show f _ = f _; rw [hclosed]⟩
  have hLpow : IsLoop (fun θ => ((c + ↑r * exp (I * ↑θ)) - ρ') ^ m') 0 (2 * Real.pi) :=
    ⟨hLlin.continuous.pow m', fun θ => pow_ne_zero _ (hLlin.nonzero θ), by simp only [hLlin.closed]⟩
  have hfeq : (fun θ : ℝ => f' (c + ↑r * exp (I * ↑θ)))
      = (fun θ : ℝ => ((c + ↑r * exp (I * ↑θ)) - ρ') ^ m' * f (c + ↑r * exp (I * ↑θ))) :=
    funext hfact'
  unfold boxCharge loopCharge
  rw [hfeq, windingNumber_mul hLpow hLf, windingNumber_pow hLlin,
    windingNumber_linear_enclosing hr hin, mul_one, wCharge_add]
  ring

/-- **Single defect charge.**  A carrier with one enclosed zero of order `m` at `ρ` (nonvanishing
cofactor `g`) has box charge `w_k(m)` — the argument principle for the boundary circle. -/
theorem boxCharge_single (k : ℕ) {f g : ℂ → ℂ} {c ρ : ℂ} {r R : ℝ} {m : ℕ}
    (hrR : r < R) (hr : 0 < r) (hin : ‖ρ - c‖ < r)
    (hgc : ContinuousOn g (Metric.ball c R)) (hg0 : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball c R, f z = (z - ρ) ^ m * g z) :
    boxCharge k f c r = wCharge (2 ^ k) (m : ℤ) := by
  have hap := loopCharge_argument_principle (f := f) (Finset.univ : Finset (Fin 1)) ![ρ] ![m]
    hrR hr (by intro i _; fin_cases i; simpa using hin) hgc hg0
    (by intro z hz; rw [hfact z hz, Fin.prod_univ_one]; simp) k
  rw [boxCharge, hap, Fin.sum_univ_one]; simp

/-- **Pair charge.**  A carrier with two enclosed zeros of orders `m₁, m₂` (nonvanishing cofactor)
has box charge `w_k(m₁) + w_k(m₂)`: the charges of the two defects add. -/
theorem boxCharge_pair (k : ℕ) {f g : ℂ → ℂ} {c ρ₁ ρ₂ : ℂ} {r R : ℝ} {m₁ m₂ : ℕ}
    (hrR : r < R) (hr : 0 < r) (hin₁ : ‖ρ₁ - c‖ < r) (hin₂ : ‖ρ₂ - c‖ < r)
    (hgc : ContinuousOn g (Metric.ball c R)) (hg0 : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball c R, f z = (z - ρ₁) ^ m₁ * (z - ρ₂) ^ m₂ * g z) :
    boxCharge k f c r = wCharge (2 ^ k) (m₁ : ℤ) + wCharge (2 ^ k) (m₂ : ℤ) := by
  have hap := loopCharge_argument_principle (f := f) (Finset.univ : Finset (Fin 2)) ![ρ₁, ρ₂] ![m₁, m₂]
    hrR hr (by intro i _; fin_cases i; exacts [by simpa using hin₁, by simpa using hin₂]) hgc hg0
    (by intro z hz; rw [hfact z hz, Fin.prod_univ_two]; simp) k
  rw [boxCharge, hap, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [wCharge_add]

/-- **Pair-annihilation rule.**  Two enclosed defects have net-zero box charge — their combined charge
can be removed through the boundary by a conserving deformation — exactly when their orders sum to a
multiple of `2^k`, i.e. `w_k(m₂) = −w_k(m₁)`.  Two defects cancel only if their charges match. -/
theorem pair_annihilation_iff (k : ℕ) {f g : ℂ → ℂ} {c ρ₁ ρ₂ : ℂ} {r R : ℝ} {m₁ m₂ : ℕ}
    (hrR : r < R) (hr : 0 < r) (hin₁ : ‖ρ₁ - c‖ < r) (hin₂ : ‖ρ₂ - c‖ < r)
    (hgc : ContinuousOn g (Metric.ball c R)) (hg0 : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball c R, f z = (z - ρ₁) ^ m₁ * (z - ρ₂) ^ m₂ * g z) :
    boxCharge k f c r = 0 ↔ (2 ^ k : ℤ) ∣ ((m₁ : ℤ) + (m₂ : ℤ)) := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [boxCharge_pair k hrR hr hin₁ hin₂ hgc hg0 hfact, ← wCharge_add, wCharge_eq_zero_iff,
    Nat.cast_pow, Nat.cast_ofNat]

/-- **Pair annihilation at the base rung is same parity.**  At `k = 1` two defects cancel exactly when
their orders have the same parity — the concrete "charges match" statement of the mod-`2` deck charge. -/
theorem pair_annihilation_level_one {f g : ℂ → ℂ} {c ρ₁ ρ₂ : ℂ} {r R : ℝ} {m₁ m₂ : ℕ}
    (hrR : r < R) (hr : 0 < r) (hin₁ : ‖ρ₁ - c‖ < r) (hin₂ : ‖ρ₂ - c‖ < r)
    (hgc : ContinuousOn g (Metric.ball c R)) (hg0 : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball c R, f z = (z - ρ₁) ^ m₁ * (z - ρ₂) ^ m₂ * g z) :
    boxCharge 1 f c r = 0 ↔ Even (m₁ + m₂) := by
  rw [pair_annihilation_iff 1 hrR hr hin₁ hin₂ hgc hg0 hfact, pow_one,
    show ((m₁ : ℤ) + (m₂ : ℤ)) = ((m₁ + m₂ : ℕ) : ℤ) by push_cast; ring,
    show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, Int.natCast_dvd_natCast, ← even_iff_two_dvd]

/-- **Conservation alone does not kill a defect.**  If the box charge of `f_0` is nontrivial, no
deformation `f_σ` keeping the boundary circle nonvanishing can remove it: `f_1` carries the same
nontrivial charge.  What decides a legal cancellation is parity/seam input, not conservation — the
bridge from the dynamic (conservation) front to the static (parity) front. -/
theorem defect_not_removable (k : ℕ) {f : ℝ → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hcont : Continuous (fun p : ℝ × ℝ => f p.1 (c + ↑r * exp (I * ↑p.2))))
    (hnv : ∀ σ θ : ℝ, f σ (c + ↑r * exp (I * ↑θ)) ≠ 0)
    (h0 : boxCharge k (f 0) c r ≠ 0) :
    boxCharge k (f 1) c r ≠ 0 := by
  rw [← boxCharge_conserved k hcont hnv]; exact h0

/-- **Two defects can cancel only if their charges match** (the dynamic pair-annihilation rule).  If a
boundary-nonvanishing deformation `f_σ` clears the two enclosed defects of `f_0` (`boxCharge (f_1) =
0`), then conservation forces `boxCharge (f_0) = 0`, so their orders sum to a multiple of `2^k`: a pair
is removable by a legal (boundary-nonvanishing) deformation only when its two charges are opposite. -/
theorem pair_cancellation_needs_matching_charge (k : ℕ) {f : ℝ → ℂ → ℂ} {g : ℂ → ℂ}
    {c ρ₁ ρ₂ : ℂ} {r R : ℝ} {m₁ m₂ : ℕ}
    (hrR : r < R) (hr : 0 < r) (hin₁ : ‖ρ₁ - c‖ < r) (hin₂ : ‖ρ₂ - c‖ < r)
    (hgc : ContinuousOn g (Metric.ball c R)) (hg0 : ∀ z ∈ Metric.ball c R, g z ≠ 0)
    (hfact0 : ∀ z ∈ Metric.ball c R, f 0 z = (z - ρ₁) ^ m₁ * (z - ρ₂) ^ m₂ * g z)
    (hcont : Continuous (fun p : ℝ × ℝ => f p.1 (c + ↑r * exp (I * ↑p.2))))
    (hnv : ∀ σ θ : ℝ, f σ (c + ↑r * exp (I * ↑θ)) ≠ 0)
    (hclear : boxCharge k (f 1) c r = 0) :
    (2 ^ k : ℤ) ∣ ((m₁ : ℤ) + (m₂ : ℤ)) := by
  have hcons := boxCharge_conserved k hcont hnv
  rw [hclear] at hcons
  exact (pair_annihilation_iff k hrR hr hin₁ hin₂ hgc hg0 hfact0).mp hcons

end RHTower
