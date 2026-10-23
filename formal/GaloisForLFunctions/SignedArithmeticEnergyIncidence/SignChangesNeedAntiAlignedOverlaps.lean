import GaloisForLFunctions.SignedArithmeticEnergyIncidence.BalancedIncidenceIsLocallyPayable

/-!
# Sign changes need anti-aligned overlaps

Which profiles create net unpaid demand in a form "positive part minus pole"?  Take the positive
part to be a signed incidence form `c` and the pole to be the square of a functional with weights
`g`, `Q(f) = E_c(f) − (Σ_i g_i f_i)²`.

* **Aligned overlaps and a positive pole: one-signed profiles are the worst**
  (`polarForm_abs_le`).  If every overlap charge of `c` is nonpositive and every polar weight is
  nonnegative, then `Q(|f|) ≤ Q(f)`: passing to the absolute value lowers the energy and raises the
  polar charge.  Hence `Q ≥ 0` iff `Q ≥ 0` on nonnegative profiles (`polarForm_nonneg_iff_of_nonneg`):
  **sign-changing profiles never create net unpaid demand** in this class.
* **The extremal adverse profile is one-signed** (`exists_nonneg_polarSolution`,
  `polarForm_nonneg_iff_polarSolution`).  If `c` is also coercive, the solution `v` of `Cv = g` is
  nonnegative (inverse positivity for a nonnegative source), `ℓ(f)² ≤ ℓ(v) E_c(f)` for every `f`,
  so `Q ≥ 0` iff `ℓ(v) ≤ 1`; when this fails, the nonnegative profile `v` is adverse.
* **Anti-aligned overlaps reward sign changes** (`signChange_beats_abs`): one positive overlap
  charge makes the alternating profile `(1, −1)` strictly cheaper than its absolute value.

So the adverse sign-changing profiles of a critical form are created exactly by its anti-aligned
overlaps — the frustrated part of its incidence — and never by a positive pole on an aligned form.
-/

open Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The polar form `E_c(f) − (Σ g_i f_i)²`. -/
def polarForm (c : ι → ι → ℝ) (g : ι → ℝ) (f : ι → ℝ) : ℝ :=
  incidenceEnergy c f - (∑ i, g i * f i) ^ 2

omit [DecidableEq ι] in
/-- A nonnegative polar weight reads at least as much on `|f|` as on `f`. -/
theorem sq_sum_le_sq_sum_abs {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) (f : ι → ℝ) :
    (∑ i, g i * f i) ^ 2 ≤ (∑ i, g i * |f i|) ^ 2 := by
  have h1 : |∑ i, g i * f i| ≤ ∑ i, g i * |f i| := by
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
    rw [abs_mul, abs_of_nonneg (hg i)]
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

omit [DecidableEq ι] in
/-- **One-signed profiles are the worst**: for aligned overlaps and a nonnegative pole,
`Q(|f|) ≤ Q(f)`. -/
theorem polarForm_abs_le {c : ι → ι → ℝ} (hz : HasNonpositiveOverlaps c) {g : ι → ℝ}
    (hg : ∀ i, 0 ≤ g i) (f : ι → ℝ) :
    polarForm c g (fun i => |f i|) ≤ polarForm c g f := by
  unfold polarForm
  have h1 := incidenceEnergy_abs_le hz f
  have h2 := sq_sum_le_sq_sum_abs hg f
  linarith

omit [DecidableEq ι] in
/-- **Sign-changing profiles never create net unpaid demand** on an aligned form with a nonnegative
pole: positivity on nonnegative profiles is positivity. -/
theorem polarForm_nonneg_iff_of_nonneg {c : ι → ι → ℝ} (hz : HasNonpositiveOverlaps c)
    {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) :
    (∀ f, 0 ≤ polarForm c g f) ↔ ∀ f, (∀ i, 0 ≤ f i) → 0 ≤ polarForm c g f := by
  constructor
  · exact fun h f _ => h f
  · intro h f
    exact le_trans (h _ fun i => abs_nonneg _) (polarForm_abs_le hz hg f)

omit [DecidableEq ι] in
/-- **Inverse positivity for a nonnegative source**: a coercive aligned form has a nonnegative
solution of `Cv = g` when `g ≥ 0`. -/
theorem exists_nonneg_polarSolution {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (hz : HasNonpositiveOverlaps c) {t : ℝ} (ht : 0 < t)
    (hcoer : ∀ f, t * ∑ i, f i ^ 2 ≤ incidenceEnergy c f) {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) :
    ∃ v : ι → ℝ, (∀ i, 0 ≤ v i) ∧ ∀ i, couplingAction c v i = g i := by
  set L := couplingActionLinear c
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hE : incidenceEnergy c f = 0 := by
      rw [incidenceEnergy_eq_sum_mul_couplingAction]
      refine sum_eq_zero fun i _ => ?_
      have : couplingAction c f i = 0 := congrFun hf i
      rw [this, mul_zero]
    have hsum : ∑ i, f i ^ 2 = 0 := by
      have h1 := hcoer f
      rw [hE] at h1
      have h2 : 0 ≤ ∑ i, f i ^ 2 := sum_nonneg fun i _ => sq_nonneg _
      nlinarith
    funext i
    have := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (f i)).mp hsum i (mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp hinj) g
  have hCv : ∀ i, couplingAction c v i = g i := fun i => congrFun hv i
  refine ⟨v, fun i => ?_, hCv⟩
  -- the absolute value is an equally good minimizer of `E(f) − 2 Σ g_i f_i`
  have hEv : incidenceEnergy c v = ∑ i, v i * g i := by
    rw [incidenceEnergy_eq_sum_mul_couplingAction]
    simp [hCv]
  have hdiff := incidenceEnergy_sub hc (fun i => |v i|) v
  have hpair : ∑ i, |v i| * couplingAction c v i = ∑ i, |v i| * g i := by simp [hCv]
  have hle : incidenceEnergy c (fun i => |v i| - v i) ≤ 0 := by
    rw [hdiff, hpair, hEv]
    have h1 := incidenceEnergy_abs_le hz v
    have h2 : ∑ i, v i * g i ≤ ∑ i, |v i| * g i :=
      sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_abs_self _) (hg i)
    rw [hEv] at h1
    linarith
  have hsq : ∑ i, (|v i| - v i) ^ 2 = 0 := by
    have h1 := hcoer (fun i => |v i| - v i)
    have h2 : 0 ≤ ∑ i, (|v i| - v i) ^ 2 := sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  have := (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (|v i| - v i)).mp hsq i (mem_univ i)
  have h0 : |v i| - v i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  have : v i = |v i| := by linarith
  rw [this]
  exact abs_nonneg _

omit [DecidableEq ι] in
/-- The polar functional is the energy pairing with the solution: `ℓ(f) = Σ_i f_i (Cv)_i`, so
`ℓ(f)² ≤ ℓ(v) E(f)` for a nonnegative form. -/
theorem polar_sq_le {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (hnn : ∀ f, 0 ≤ incidenceEnergy c f) {g v : ι → ℝ} (hv : ∀ i, couplingAction c v i = g i)
    (f : ι → ℝ) : (∑ i, g i * f i) ^ 2 ≤ (∑ i, g i * v i) * incidenceEnergy c f := by
  -- Cauchy–Schwarz for the nonnegative symmetric pairing `B(x, y) = Σ_i x_i (Cy)_i`
  have hB : ∀ s : ℝ, 0 ≤ incidenceEnergy c (fun i => f i - s * v i) := fun s => hnn _
  have hexp : ∀ s : ℝ, incidenceEnergy c (fun i => f i - s * v i) =
      incidenceEnergy c f - 2 * s * (∑ i, g i * f i) + s ^ 2 * (∑ i, g i * v i) := by
    intro s
    have h := incidenceEnergy_sub hc f (fun i => s * v i)
    have hact : ∀ i, couplingAction c (fun j => s * v j) i = s * g i := by
      intro i
      unfold couplingAction
      rw [← hv i, couplingAction, mul_sum]
      exact sum_congr rfl fun j _ => by ring
    have h2 : ∑ i, f i * couplingAction c (fun j => s * v j) i = s * ∑ i, g i * f i := by
      simp only [hact, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    have h3 : incidenceEnergy c (fun i => s * v i) = s ^ 2 * ∑ i, g i * v i := by
      rw [incidenceEnergy_eq_sum_mul_couplingAction]
      simp only [hact, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    rw [h, h2, h3]
    ring
  set a := ∑ i, g i * v i
  set b := ∑ i, g i * f i
  set e := incidenceEnergy c f
  have he : 0 ≤ e := hnn f
  have hq : ∀ s : ℝ, 0 ≤ e - 2 * s * b + s ^ 2 * a := fun s => by rw [← hexp s]; exact hB s
  have ha : 0 ≤ a := by
    have := hnn v
    rw [incidenceEnergy_eq_sum_mul_couplingAction] at this
    simpa [hv, mul_comm] using this
  rcases ha.eq_or_lt with ha0 | hapos
  · -- `a = 0`: the quadratic is linear in `s`, so `b = 0`
    have hb : b = 0 := by
      by_contra hb
      have h3 := hq ((e + 1) / (2 * b))
      have h4 : e - 2 * ((e + 1) / (2 * b)) * b + ((e + 1) / (2 * b)) ^ 2 * a = -1 := by
        rw [← ha0]; field_simp; ring
      linarith
    rw [hb, ← ha0]; simp
  · have := hq (b / a)
    have h2 : e - 2 * (b / a) * b + (b / a) ^ 2 * a = e - b ^ 2 / a := by field_simp; ring
    rw [h2, sub_nonneg, div_le_iff₀ hapos] at this
    linarith

omit [DecidableEq ι] in
/-- **The extremal adverse profile is one-signed.**  For a coercive aligned form and a nonnegative
pole with solution `Cv = g`, `v ≥ 0`: the polar form is nonnegative iff `ℓ(v) ≤ 1`, and otherwise
`v` itself is adverse. -/
theorem polarForm_nonneg_iff_polarSolution {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c)
    (hnn : ∀ f, 0 ≤ incidenceEnergy c f) {g v : ι → ℝ} (hv : ∀ i, couplingAction c v i = g i) :
    (∀ f, 0 ≤ polarForm c g f) ↔ ∑ i, g i * v i ≤ 1 := by
  have hEv : incidenceEnergy c v = ∑ i, g i * v i := by
    rw [incidenceEnergy_eq_sum_mul_couplingAction]
    simp [hv, mul_comm]
  constructor
  · intro h
    have := h v
    unfold polarForm at this
    rw [hEv] at this
    have ha : 0 ≤ ∑ i, g i * v i := by rw [← hEv]; exact hnn v
    nlinarith
  · intro h f
    unfold polarForm
    have h1 := polar_sq_le hc hnn hv f
    have h2 := hnn f
    nlinarith

/-- **Anti-aligned overlaps reward sign changes**: with a positive overlap charge between `i` and
`j`, the alternating profile is strictly cheaper than its absolute value. -/
theorem signChange_beats_abs {c : ι → ι → ℝ} (hc : IsSymmetricCoupling c) {i j : ι} (hij : i ≠ j)
    (hpos : 0 < c i j) :
    incidenceEnergy c (fun k => if k = i then 1 else if k = j then -1 else 0) <
      incidenceEnergy c (fun k => |if k = i then (1 : ℝ) else if k = j then -1 else 0|) := by
  set f : ι → ℝ := fun k => if k = i then 1 else if k = j then -1 else 0 with hf
  have hfi : f i = 1 := by simp [hf]
  have hfj : f j = -1 := by simp [hf, Ne.symm hij]
  have hfk : ∀ k, k ≠ i → k ≠ j → f k = 0 := fun k hki hkj => by simp [hf, hki, hkj]
  -- both energies only see the two points `i, j`
  have hE : ∀ h : ι → ℝ, (∀ k, k ≠ i → k ≠ j → h k = 0) →
      incidenceEnergy c h = c i i * h i ^ 2 + 2 * c i j * h i * h j + c j j * h j ^ 2 := by
    intro h hz
    unfold incidenceEnergy
    have hrow : ∀ k, ∑ l, c k l * h k * h l = c k i * h k * h i + c k j * h k * h j := by
      intro k
      rw [← sum_subset (subset_univ {i, j})]
      · rw [sum_pair hij]
      · intro l _ hl
        simp only [mem_insert, mem_singleton, not_or] at hl
        rw [hz l hl.1 hl.2, mul_zero]
    simp only [hrow]
    rw [← sum_subset (subset_univ {i, j})]
    · rw [sum_pair hij, hc j i]; ring
    · intro k _ hk
      simp only [mem_insert, mem_singleton, not_or] at hk
      rw [hz k hk.1 hk.2]; ring
  rw [hE f hfk, hE (fun k => |f k|) fun k hki hkj => by rw [hfk k hki hkj, abs_zero]]
  simp only [hfi, hfj, abs_one, abs_neg]
  linarith

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
