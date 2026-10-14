import GaloisForLFunctions.HTGeometry.CaratheodoryCoefficient

/-!
# Exponential sums with nonnegative real part have bounded power sums

Let `f(u) = Σ_i w_i e^{S_i u}`, a finite or absolutely summable family with bounded exponents.  If
`Re f ≥ 0` on the circle `|u| = R`, then for every `n ≥ 1`

`|Σ_i w_i S_i^n| R^n ≤ 2 n! Re Σ_i w_i`

(`norm_sum_mul_pow_mul_pow_le`, `norm_tsum_mul_pow_mul_pow_le`).  The Taylor coefficients of `f` at
`0` are `Σ_i w_i S_i^n/n!`, and Carathéodory's coefficient inequality bounds them by twice the real
part at the centre.

**Coherent families.**  If all `w_i ≥ 0` and all `S_i ≥ 0` are real, the power sums cannot cancel,
and every single term obeys the *weight penalty* `w_j (R S_j)^n ≤ 2 n! Σ_i w_i`
(`weight_mul_pow_le_of_coherent`).  Taking `n ≈ R S_j` gives `w_j ≲ e^{−R S_j}`: a member of a
coherent family can only stay hidden behind a positive real part if its weight is exponentially
small in its exponent.

**Mixed families.**  If only the members of a set `C` are coherent and the others have `|S_i| ≤ M`,
the incoherent part can cancel at most its own trivial size, so every coherent member with
`S_j ≥ max(eM, e/R)` satisfies `w_j ≤ e (2 Re Σ w + Σ_{i∉C} |w_i|) e^{−R S_j/e}`
(`coherent_weight_le_exp_mixed`).  Exponentially penalized members with `Σ w^θ < ∞` (`θ < 1`) have
negligible total effect at every small amplitude: `Σ_{i∈D} w_i e^{x S_i} ≤ K^{1−θ} (Σ w^θ)
e^{−(1−θ) R T/(2e)}` for `x ≤ (1−θ)R/(2e)` (`tsum_penalized_mul_exp_le`).  So a coherent family of
large exponents can never hide a target of smaller exponent from an anti-aligning amplitude.
-/

open Complex Metric Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The exponential sum `u ↦ Σ_{i ∈ s} w_i e^{S_i u}`. -/
def caratheodoryExpSum {ι : Type*} (s : Finset ι) (w S : ι → ℂ) (u : ℂ) : ℂ :=
  ∑ i ∈ s, w i * cexp (S i * u)

theorem differentiable_caratheodoryExpSum {ι : Type*} (s : Finset ι) (w S : ι → ℂ) :
    Differentiable ℂ (caratheodoryExpSum s w S) := by
  unfold caratheodoryExpSum
  fun_prop

theorem caratheodoryExpSum_zero {ι : Type*} (s : Finset ι) (w S : ι → ℂ) :
    caratheodoryExpSum s w S 0 = ∑ i ∈ s, w i := by
  simp [caratheodoryExpSum]

/-- The `n`-th derivative at `0` is the `n`-th power sum. -/
theorem iteratedDeriv_caratheodoryExpSum_zero {ι : Type*} (s : Finset ι) (w S : ι → ℂ) (n : ℕ) :
    iteratedDeriv n (caratheodoryExpSum s w S) 0 = ∑ i ∈ s, w i * S i ^ n := by
  have hfun : caratheodoryExpSum s w S = fun u => ∑ i ∈ s, w i * cexp (S i * u) := rfl
  rw [hfun, iteratedDeriv_fun_sum (fun i _ => by fun_prop)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_const_mul (w i) (by fun_prop), iteratedDeriv_cexp_const_mul]
  simp

/-- The Cauchy coefficients of the exponential sum are its power sums over `n!`. -/
theorem cauchyCoeff_caratheodoryExpSum {ι : Type*} (s : Finset ι) (w S : ι → ℂ) {R : ℝ}
    (hR : 0 < R) (n : ℕ) :
    cauchyCoeff (caratheodoryExpSum s w S) R n = (∑ i ∈ s, w i * S i ^ n) / n.factorial := by
  obtain ⟨Rn, hRn⟩ : ∃ Rn : NNReal, (Rn : ℝ) = R := ⟨⟨R, hR.le⟩, rfl⟩
  have hRn0 : 0 < Rn := by rw [← NNReal.coe_pos, hRn]; exact hR
  have hf : DiffContOnCl ℂ (caratheodoryExpSum s w S) (ball 0 (Rn : ℝ)) :=
    (differentiable_caratheodoryExpSum s w S).diffContOnCl
  have hps := hf.hasFPowerSeriesOnBall hRn0
  have hfac := hps.factorial_smul 1 n
  rw [← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_caratheodoryExpSum_zero, nsmul_eq_mul]
    at hfac
  have hfac0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [cauchyCoeff, ← hRn, eq_div_iff hfac0, mul_comm, hfac]

/-- **Power sums of a positive exponential sum.**  If `Re Σ_i w_i e^{S_i u} ≥ 0` on `|u| = R`,
then `|Σ_i w_i S_i^n| R^n ≤ 2 n! Re Σ_i w_i` for every `n ≥ 1`. -/
theorem norm_sum_mul_pow_mul_pow_le {ι : Type*} (s : Finset ι) (w S : ι → ℂ) {R : ℝ}
    (hR : 0 < R) (hpos : ∀ u ∈ sphere (0 : ℂ) R, 0 ≤ (caratheodoryExpSum s w S u).re)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖∑ i ∈ s, w i * S i ^ n‖ * R ^ n ≤ 2 * n.factorial * (∑ i ∈ s, w i).re := by
  have hc := norm_cauchyCoeff_mul_pow_le (caratheodoryExpSum s w S) hR
    (differentiable_caratheodoryExpSum s w S).diffContOnCl hpos hn
  rw [cauchyCoeff_caratheodoryExpSum s w S hR, caratheodoryExpSum_zero, norm_div] at hc
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [show ‖(n.factorial : ℂ)‖ = (n.factorial : ℝ) by simp] at hc
  rw [div_mul_eq_mul_div, div_le_iff₀ hfac] at hc
  linarith

/-- **Weight penalty for coherent families.**  If all `w_i ≥ 0` and `S_i ≥ 0` are real and
`Re Σ_i w_i e^{S_i u} ≥ 0` on `|u| = R`, then every member satisfies
`w_j (R S_j)^n ≤ 2 n! Σ_i w_i`. -/
theorem weight_mul_pow_le_of_coherent {ι : Type*} (s : Finset ι) (w S : ι → ℝ) {R : ℝ}
    (hR : 0 < R) (hw : ∀ i ∈ s, 0 ≤ w i) (hS : ∀ i ∈ s, 0 ≤ S i)
    (hpos : ∀ u ∈ sphere (0 : ℂ) R,
      0 ≤ (caratheodoryExpSum s (fun i => (w i : ℂ)) (fun i => (S i : ℂ)) u).re)
    {n : ℕ} (hn : 1 ≤ n) {j : ι} (hj : j ∈ s) :
    w j * (R * S j) ^ n ≤ 2 * n.factorial * ∑ i ∈ s, w i := by
  have h := norm_sum_mul_pow_mul_pow_le s (fun i => (w i : ℂ)) (fun i => (S i : ℂ)) hR hpos hn
  have hreal : ∑ i ∈ s, (w i : ℂ) * (S i : ℂ) ^ n = ((∑ i ∈ s, w i * S i ^ n : ℝ) : ℂ) := by
    push_cast; rfl
  have hnn : 0 ≤ ∑ i ∈ s, w i * S i ^ n :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (pow_nonneg (hS i hi) n)
  rw [hreal, Complex.norm_real, Real.norm_of_nonneg hnn] at h
  have hre : (∑ i ∈ s, (w i : ℂ)).re = ∑ i ∈ s, w i := by
    rw [Complex.re_sum]; simp
  rw [hre] at h
  have hterm : w j * S j ^ n ≤ ∑ i ∈ s, w i * S i ^ n :=
    Finset.single_le_sum (f := fun i => w i * S i ^ n)
      (fun i hi => mul_nonneg (hw i hi) (pow_nonneg (hS i hi) n)) hj
  have hRn : 0 ≤ R ^ n := pow_nonneg hR.le n
  calc w j * (R * S j) ^ n = w j * S j ^ n * R ^ n := by ring
    _ ≤ (∑ i ∈ s, w i * S i ^ n) * R ^ n := mul_le_mul_of_nonneg_right hterm hRn
    _ ≤ 2 * n.factorial * ∑ i ∈ s, w i := h

/-! ## Summable families -/

/-- **Power sums of a positive summable exponential sum.**  Let `Σ_i ‖w_i‖ < ∞` and `‖S_i‖ ≤ B`.
If `Re Σ'_i w_i e^{S_i u} ≥ 0` on `|u| = R`, then `|Σ'_i w_i S_i^n| R^n ≤ 2 n! Re Σ'_i w_i` for every
`n ≥ 1`. -/
theorem norm_tsum_mul_pow_mul_pow_le {ι : Type*} (w S : ι → ℂ) {B R : ℝ} (hR : 0 < R)
    (hw : Summable fun i => ‖w i‖) (hB0 : 0 ≤ B) (hB : ∀ i, ‖S i‖ ≤ B)
    (hpos : ∀ u ∈ sphere (0 : ℂ) R, 0 ≤ (∑' i, w i * cexp (S i * u)).re)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖∑' i, w i * S i ^ n‖ * R ^ n ≤ 2 * n.factorial * (∑' i, w i).re := by
  classical
  -- a uniform bound for the terms on the circle
  have hterm : ∀ i, ∀ u : ℂ, ‖u‖ ≤ R → ‖w i * cexp (S i * u)‖ ≤ ‖w i‖ * Real.exp (B * R) := by
    intro i u hu
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
    rw [norm_mul]
    exact mul_le_mul (hB i) hu (norm_nonneg _) hB0
  have hpow : ∀ i, ‖w i * S i ^ n‖ ≤ ‖w i‖ * B ^ n := fun i => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hB i) n) (norm_nonneg _)
  have hsumpow : Summable fun i => w i * S i ^ n :=
    Summable.of_norm_bounded (hw.mul_right (B ^ n)) hpow
  have hsumw : Summable w := Summable.of_norm hw
  -- the tails of the weights
  obtain ⟨T, hT⟩ : ∃ T : Finset ι → ℝ, T = fun F => ∑' i : {x // x ∉ F}, ‖w i‖ := ⟨_, rfl⟩
  have hTlim : Tendsto T atTop (𝓝 0) := by
    rw [hT]; exact tendsto_tsum_compl_atTop_zero fun i => ‖w i‖
  -- the finite inequality with the tail added to the centre value
  have hfin : ∀ F : Finset ι, ‖∑ i ∈ F, w i * S i ^ n‖ * R ^ n ≤
      2 * n.factorial * ((∑ i ∈ F, w i).re + T F * Real.exp (B * R)) := by
    intro F
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = T F * Real.exp (B * R) := ⟨_, rfl⟩
    have hc0 : 0 ≤ c := by
      rw [hc, hT]; exact mul_nonneg (tsum_nonneg fun _ => norm_nonneg _) (Real.exp_pos _).le
    -- the family on `F` together with one constant term
    let w' : Option ι → ℂ := fun o => o.elim (c : ℂ) w
    let S' : Option ι → ℂ := fun o => o.elim 0 S
    have hpos' : ∀ u ∈ sphere (0 : ℂ) R,
        0 ≤ (caratheodoryExpSum (Finset.insertNone F) w' S' u).re := by
      intro u hu
      have hu' : ‖u‖ = R := by simpa using hu
      have hsplit : caratheodoryExpSum (Finset.insertNone F) w' S' u =
          (c : ℂ) + ∑ i ∈ F, w i * cexp (S i * u) := by
        simp [caratheodoryExpSum, w', S', Finset.sum_insertNone]
      have htot := hpos u hu
      have hsummn : Summable fun i => ‖w i * cexp (S i * u)‖ :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hterm i u hu'.le)
          (hw.mul_right _)
      have hsumm : Summable fun i => w i * cexp (S i * u) := hsummn.of_norm
      rw [← hsumm.sum_add_tsum_subtype_compl F, Complex.add_re] at htot
      have htail : ‖∑' i : {x // x ∉ F}, w i * cexp (S i * u)‖ ≤ c := by
        rw [hc, hT]
        calc ‖∑' i : {x // x ∉ F}, w i * cexp (S i * u)‖
            ≤ ∑' i : {x // x ∉ F}, ‖w i * cexp (S i * u)‖ :=
              norm_tsum_le_tsum_norm (hsummn.subtype _)
          _ ≤ ∑' i : {x // x ∉ F}, ‖w i‖ * Real.exp (B * R) :=
              Summable.tsum_le_tsum (fun i => hterm i u hu'.le) (hsummn.subtype _)
                ((hw.subtype _).mul_right _)
          _ = (∑' i : {x // x ∉ F}, ‖w i‖) * Real.exp (B * R) := tsum_mul_right
      have hre := Complex.re_le_norm (∑' i : {x // x ∉ F}, w i * cexp (S i * u))
      rw [hsplit, Complex.add_re, Complex.ofReal_re]
      linarith
    have h := norm_sum_mul_pow_mul_pow_le (Finset.insertNone F) w' S' hR hpos' hn
    have hn0 : (0 : ℂ) ^ n = 0 := zero_pow (by omega)
    have e1 : ∑ i ∈ Finset.insertNone F, w' i * S' i ^ n = ∑ i ∈ F, w i * S i ^ n := by
      simp [w', S', Finset.sum_insertNone, hn0]
    have e2 : (∑ i ∈ Finset.insertNone F, w' i).re = c + (∑ i ∈ F, w i).re := by
      simp [w', Finset.sum_insertNone, Complex.re_sum]
    rw [e1, e2] at h
    rw [← hc]; linarith
  -- pass to the limit along finite sets
  have hlim1 : Tendsto (fun F : Finset ι => ‖∑ i ∈ F, w i * S i ^ n‖ * R ^ n) atTop
      (𝓝 (‖∑' i, w i * S i ^ n‖ * R ^ n)) :=
    (hsumpow.hasSum.norm).mul_const _
  have hlim2 : Tendsto (fun F : Finset ι =>
      2 * n.factorial * ((∑ i ∈ F, w i).re + T F * Real.exp (B * R))) atTop
      (𝓝 (2 * n.factorial * ((∑' i, w i).re + 0 * Real.exp (B * R)))) := by
    refine Tendsto.const_mul _ (Tendsto.add ?_ (hTlim.mul_const _))
    exact (Complex.continuous_re.tendsto _).comp hsumw.hasSum
  have h := le_of_tendsto_of_tendsto' hlim1 hlim2 hfin
  simpa using h

/-- **Weight penalty for summable coherent families.**  Let `w_i ≥ 0` be summable and
`0 ≤ S_i ≤ B` real.  If `Re Σ'_i w_i e^{S_i u} ≥ 0` on `|u| = R`, then every member satisfies
`w_j (R S_j)^n ≤ 2 n! Σ'_i w_i` for every `n ≥ 1`. -/
theorem weight_mul_pow_le_of_coherent_tsum {ι : Type*} (w S : ι → ℝ) {B R : ℝ} (hR : 0 < R)
    (hw0 : ∀ i, 0 ≤ w i) (hw : Summable w) (hS0 : ∀ i, 0 ≤ S i) (hB : ∀ i, S i ≤ B)
    (hpos : ∀ u ∈ sphere (0 : ℂ) R, 0 ≤ (∑' i, (w i : ℂ) * cexp ((S i : ℂ) * u)).re)
    {n : ℕ} (hn : 1 ≤ n) (j : ι) :
    w j * (R * S j) ^ n ≤ 2 * n.factorial * ∑' i, w i := by
  have hB0 : 0 ≤ B := (hS0 j).trans (hB j)
  have hwn : Summable fun i => ‖(w i : ℂ)‖ := by
    simpa [Complex.norm_real, Real.norm_of_nonneg (hw0 _)] using hw
  have hSn : ∀ i, ‖(S i : ℂ)‖ ≤ B := fun i => by
    rw [Complex.norm_real, Real.norm_of_nonneg (hS0 i)]; exact hB i
  have h := norm_tsum_mul_pow_mul_pow_le (fun i => (w i : ℂ)) (fun i => (S i : ℂ)) hR hwn hB0 hSn
    hpos hn
  have hsumpow : Summable fun i => w i * S i ^ n :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 i) (pow_nonneg (hS0 i) n))
      (fun i => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hS0 i) (hB i) n) (hw0 i))
      (hw.mul_right (B ^ n))
  have hreal : ∑' i, (w i : ℂ) * (S i : ℂ) ^ n = ((∑' i, w i * S i ^ n : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; push_cast; rfl
  have hnn : 0 ≤ ∑' i, w i * S i ^ n :=
    tsum_nonneg fun i => mul_nonneg (hw0 i) (pow_nonneg (hS0 i) n)
  rw [hreal, Complex.norm_real, Real.norm_of_nonneg hnn] at h
  have hre : (∑' i, (w i : ℂ)).re = ∑' i, w i := by
    rw [← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [hre] at h
  have hterm : w j * S j ^ n ≤ ∑' i, w i * S i ^ n :=
    hsumpow.le_tsum j fun i _ => mul_nonneg (hw0 i) (pow_nonneg (hS0 i) n)
  calc w j * (R * S j) ^ n = w j * S j ^ n * R ^ n := by ring
    _ ≤ (∑' i, w i * S i ^ n) * R ^ n := mul_le_mul_of_nonneg_right hterm (pow_nonneg hR.le n)
    _ ≤ 2 * n.factorial * ∑' i, w i := h

/-! ## Mixed families: coherent members pay an exponential penalty -/

theorem re_mul_pow_of_im_eq_zero {w S : ℂ} (hw : w.im = 0) (hS : S.im = 0) (n : ℕ) :
    (w * S ^ n).re = w.re * S.re ^ n := by
  have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hw])
  have hS' : S = (S.re : ℂ) := Complex.ext (by simp) (by simp [hS])
  rw [hw', hS']
  simp only [Complex.ofReal_re]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- **Coherent members of a positive mixed family.**  Let `Re Σ'_i w_i e^{S_i u} ≥ 0` on `|u| = R`,
with `Σ‖w_i‖ < ∞` and `‖S_i‖ ≤ B`.  Let the members of `C` be coherent (`w_i, S_i` real and
nonnegative) and the others have `‖S_i‖ ≤ M`.  Then every coherent member satisfies
`w_j (R S_j)^n ≤ 2 n! Re Σ'_i w_i + (R M)^n Σ_{i∉C} ‖w_i‖`: the incoherent part can cancel at most
its own trivial size. -/
theorem coherent_weight_mul_pow_le_mixed {ι : Type*} (w S : ι → ℂ) (C : Set ι) {B M R : ℝ}
    (hR : 0 < R) (hw : Summable fun i => ‖w i‖) (hB0 : 0 ≤ B) (hB : ∀ i, ‖S i‖ ≤ B)
    (hM : ∀ i, i ∉ C → ‖S i‖ ≤ M)
    (hcoh : ∀ i ∈ C, (w i).im = 0 ∧ 0 ≤ (w i).re ∧ (S i).im = 0 ∧ 0 ≤ (S i).re)
    (hpos : ∀ u ∈ sphere (0 : ℂ) R, 0 ≤ (∑' i, w i * cexp (S i * u)).re)
    {n : ℕ} (hn : 1 ≤ n) {j : ι} (hj : j ∈ C) :
    (w j).re * (R * (S j).re) ^ n ≤
      2 * n.factorial * (∑' i, w i).re + (R * M) ^ n * ∑' i : ↥Cᶜ, ‖w i‖ := by
  have h := norm_tsum_mul_pow_mul_pow_le w S hR hw hB0 hB hpos hn
  have hpow : ∀ i, ‖w i * S i ^ n‖ ≤ ‖w i‖ * B ^ n := fun i => by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hB i) n) (norm_nonneg _)
  have hsumn : Summable fun i => ‖w i * S i ^ n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpow (hw.mul_right _)
  have hsum : Summable fun i => w i * S i ^ n := hsumn.of_norm
  rw [← hsum.tsum_subtype_add_tsum_subtype_compl C] at h
  -- the coherent part dominates its member `j`
  have hCsum : Summable fun i : ↥C => w i * S i ^ n := hsum.subtype _
  have hCre : (w j).re * (S j).re ^ n ≤ (∑' i : ↥C, w i * S i ^ n).re := by
    rw [Complex.re_tsum hCsum]
    have hnn : ∀ i : ↥C, 0 ≤ (w i * S i ^ n).re := fun i => by
      obtain ⟨h1, h2, h3, h4⟩ := hcoh i i.2
      rw [re_mul_pow_of_im_eq_zero h1 h3]
      exact mul_nonneg h2 (pow_nonneg h4 n)
    have hj' := (Complex.hasSum_re hCsum.hasSum).summable.le_tsum ⟨j, hj⟩ fun i _ => hnn i
    obtain ⟨h1, -, h3, -⟩ := hcoh j hj
    rw [re_mul_pow_of_im_eq_zero h1 h3] at hj'
    exact hj'
  -- the incoherent part is at most its trivial size
  have hCc : ‖∑' i : ↥Cᶜ, w i * S i ^ n‖ ≤ M ^ n * ∑' i : ↥Cᶜ, ‖w i‖ := by
    have hb : ∀ i : ↥Cᶜ, ‖w i * S i ^ n‖ ≤ M ^ n * ‖w i‖ := fun i => by
      rw [norm_mul, norm_pow, mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM i i.2) n)
        (norm_nonneg _)
    calc ‖∑' i : ↥Cᶜ, w i * S i ^ n‖ ≤ ∑' i : ↥Cᶜ, ‖w i * S i ^ n‖ :=
          norm_tsum_le_tsum_norm (hsumn.subtype _)
      _ ≤ ∑' i : ↥Cᶜ, M ^ n * ‖w i‖ :=
          Summable.tsum_le_tsum hb (hsumn.subtype _) ((hw.subtype _).mul_left _)
      _ = M ^ n * ∑' i : ↥Cᶜ, ‖w i‖ := tsum_mul_left
  have htot := norm_add_le (∑' i : ↥C, w i * S i ^ n) (∑' i : ↥Cᶜ, w i * S i ^ n)
  have hre1 := Complex.re_le_norm (∑' i : ↥C, w i * S i ^ n)
  have hdiff : ‖∑' i : ↥C, w i * S i ^ n‖ ≤
      ‖∑' i : ↥C, w i * S i ^ n + ∑' i : ↥Cᶜ, w i * S i ^ n‖ + ‖∑' i : ↥Cᶜ, w i * S i ^ n‖ := by
    have := norm_sub_le (∑' i : ↥C, w i * S i ^ n + ∑' i : ↥Cᶜ, w i * S i ^ n)
      (∑' i : ↥Cᶜ, w i * S i ^ n)
    rwa [add_sub_cancel_right] at this
  have hRn : 0 ≤ R ^ n := pow_nonneg hR.le n
  have key : (w j).re * (S j).re ^ n ≤
      ‖∑' i : ↥C, w i * S i ^ n + ∑' i : ↥Cᶜ, w i * S i ^ n‖ + M ^ n * ∑' i : ↥Cᶜ, ‖w i‖ := by
    linarith
  have key2 := mul_le_mul_of_nonneg_right key hRn
  calc (w j).re * (R * (S j).re) ^ n = (w j).re * (S j).re ^ n * R ^ n := by ring
    _ ≤ (‖∑' i : ↥C, w i * S i ^ n + ∑' i : ↥Cᶜ, w i * S i ^ n‖ +
          M ^ n * ∑' i : ↥Cᶜ, ‖w i‖) * R ^ n := key2
    _ = ‖∑' i : ↥C, w i * S i ^ n + ∑' i : ↥Cᶜ, w i * S i ^ n‖ * R ^ n +
          (R * M) ^ n * ∑' i : ↥Cᶜ, ‖w i‖ := by ring
    _ ≤ 2 * n.factorial * (∑' i, w i).re + (R * M) ^ n * ∑' i : ↥Cᶜ, ‖w i‖ := by linarith

/-- **Exponential penalty for coherent members of a positive mixed family.**  Under the hypotheses
of `coherent_weight_mul_pow_le_mixed`, every coherent member with `S_j ≥ max(eM, e/R)` satisfies
`w_j ≤ e (2 Re Σ'_i w_i + Σ_{i∉C} ‖w_i‖) e^{−R S_j/e}`. -/
theorem coherent_weight_le_exp_mixed {ι : Type*} (w S : ι → ℂ) (C : Set ι) {B M R : ℝ}
    (hR : 0 < R) (hw : Summable fun i => ‖w i‖) (hB0 : 0 ≤ B) (hB : ∀ i, ‖S i‖ ≤ B)
    (hM0 : 0 ≤ M) (hM : ∀ i, i ∉ C → ‖S i‖ ≤ M)
    (hcoh : ∀ i ∈ C, (w i).im = 0 ∧ 0 ≤ (w i).re ∧ (S i).im = 0 ∧ 0 ≤ (S i).re)
    (hpos : ∀ u ∈ sphere (0 : ℂ) R, 0 ≤ (∑' i, w i * cexp (S i * u)).re)
    {j : ι} (hj : j ∈ C) (hSM : Real.exp 1 * M ≤ (S j).re) (hSR : Real.exp 1 ≤ R * (S j).re) :
    (w j).re ≤ Real.exp 1 * (2 * (∑' i, w i).re + ∑' i : ↥Cᶜ, ‖w i‖) *
      Real.exp (-(R * (S j).re) / Real.exp 1) := by
  obtain ⟨-, hwj0, -, hSj0⟩ := hcoh j hj
  have he := Real.exp_pos 1
  have he1 : 1 < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = R * (S j).re := ⟨_, rfl⟩
  rw [← hx] at hSR ⊢
  have hx0 : 0 < x := lt_of_lt_of_le he hSR
  have hS0 : 0 < (S j).re := by
    rw [hx] at hx0; exact pos_of_mul_pos_right hx0 hR.le
  -- the exponent `k = ⌊x/e⌋`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊x / Real.exp 1⌋₊ := ⟨_, rfl⟩
  have hxe : 1 ≤ x / Real.exp 1 := by rw [le_div_iff₀ he]; linarith
  have hk1 : 1 ≤ k := by rw [hk]; exact (Nat.one_le_floor_iff _).mpr hxe
  have hkle : (k : ℝ) ≤ x / Real.exp 1 := by rw [hk]; exact Nat.floor_le (by positivity)
  have hklt : x / Real.exp 1 < k + 1 := by rw [hk]; exact Nat.lt_floor_add_one _
  -- Re Σ' w ≥ 0
  have hW0 : 0 ≤ (∑' i, w i).re := by
    have h1 := norm_tsum_mul_pow_mul_pow_le w S hR hw hB0 hB hpos le_rfl
    have : 0 ≤ ‖∑' i, w i * S i ^ 1‖ * R ^ 1 := by positivity
    simp only [Nat.factorial_one, Nat.cast_one, mul_one] at h1
    linarith
  have hWc0 : 0 ≤ ∑' i : ↥Cᶜ, ‖w i‖ := tsum_nonneg fun _ => norm_nonneg _
  have h := coherent_weight_mul_pow_le_mixed w S C hR hw hB0 hB hM hcoh hpos hk1 hj
  rw [← hx] at h
  have hxk : 0 < x ^ k := pow_pos hx0 k
  -- `k!/x^k ≤ e^{−k}` and `(RM/x)^k ≤ e^{−k}`
  have hfac : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
  have hkx : (k : ℝ) / x ≤ Real.exp (-1) := by
    rw [Real.exp_neg, div_le_iff₀ hx0, ← div_eq_inv_mul, le_div_iff₀ he]
    rw [le_div_iff₀ he] at hkle; linarith
  have hRMx : R * M / x ≤ Real.exp (-1) := by
    rw [Real.exp_neg, div_le_iff₀ hx0, ← div_eq_inv_mul, le_div_iff₀ he, hx]
    nlinarith
  have hpow1 : ((k : ℝ) / x) ^ k ≤ Real.exp (-1) ^ k :=
    pow_le_pow_left₀ (by positivity) hkx k
  have hpow2 : (R * M / x) ^ k ≤ Real.exp (-1) ^ k :=
    pow_le_pow_left₀ (by positivity) hRMx k
  have hek : Real.exp (-1) ^ k ≤ Real.exp 1 * Real.exp (-x / Real.exp 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have : -(x / Real.exp 1) < -(k : ℝ) + 1 := by linarith
    rw [neg_div]; linarith
  -- divide the power inequality by `x^k`
  have hdiv : (w j).re ≤ 2 * (∑' i, w i).re * ((k : ℝ) / x) ^ k +
      (∑' i : ↥Cᶜ, ‖w i‖) * (R * M / x) ^ k := by
    rw [div_pow, div_pow]
    have h' : (w j).re * x ^ k ≤ 2 * (k : ℝ) ^ k * (∑' i, w i).re +
        (R * M) ^ k * ∑' i : ↥Cᶜ, ‖w i‖ := by
      have := mul_le_mul_of_nonneg_right hfac (show (0 : ℝ) ≤ 2 * (∑' i, w i).re by linarith)
      nlinarith
    rw [← mul_le_mul_iff_of_pos_right hxk]
    have e : (2 * (∑' i, w i).re * ((k : ℝ) ^ k / x ^ k) +
        (∑' i : ↥Cᶜ, ‖w i‖) * ((R * M) ^ k / x ^ k)) * x ^ k =
        2 * (k : ℝ) ^ k * (∑' i, w i).re + (R * M) ^ k * ∑' i : ↥Cᶜ, ‖w i‖ := by
      field_simp
    rw [e]; exact h'
  have h1 := mul_le_mul_of_nonneg_left hpow1 (show (0 : ℝ) ≤ 2 * (∑' i, w i).re by linarith)
  have h2 := mul_le_mul_of_nonneg_left hpow2 hWc0
  have h3 : (2 * (∑' i, w i).re + ∑' i : ↥Cᶜ, ‖w i‖) * Real.exp (-1) ^ k ≤
      (2 * (∑' i, w i).re + ∑' i : ↥Cᶜ, ‖w i‖) * (Real.exp 1 * Real.exp (-x / Real.exp 1)) :=
    mul_le_mul_of_nonneg_left hek (by linarith)
  nlinarith

/-- **Exponentially penalized members cannot hide anything.**  Let `v_i ≥ 0` with
`Σ v_i^θ < ∞` for some `θ ∈ (0, 1)`, and let every `i ∈ D` satisfy `v_i ≤ K e^{−R s_i/e}` with
`s_i ≥ T ≥ 0`.  Then for `x ≤ (1 − θ) R/(2e)`,
`Σ_{i ∈ D} v_i e^{x s_i} ≤ K^{1−θ} (Σ_i v_i^θ) e^{−(1−θ) R T/(2e)}`. -/
theorem tsum_penalized_mul_exp_le {ι : Type*} (v s : ι → ℝ) (D : Set ι) {K R θ T x : ℝ}
    (hv0 : ∀ i, 0 ≤ v i) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hsumθ : Summable fun i => v i ^ θ)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hpen : ∀ i ∈ D, v i ≤ K * Real.exp (-(R * s i) / Real.exp 1))
    (hsT : ∀ i ∈ D, T ≤ s i) (hxR : x ≤ (1 - θ) * R / (2 * Real.exp 1)) :
    ∑' i : ↥D, v i * Real.exp (x * s i) ≤
      K ^ (1 - θ) * (∑' i, v i ^ θ) * Real.exp (-((1 - θ) * R * T) / (2 * Real.exp 1)) := by
  have he := Real.exp_pos 1
  have h1θ : 0 < 1 - θ := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = K ^ (1 - θ) * Real.exp (-((1 - θ) * R * T) / (2 * Real.exp 1)) :=
    ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; exact mul_nonneg (Real.rpow_nonneg hK _) (Real.exp_pos _).le
  have hterm : ∀ i : ↥D, v i * Real.exp (x * s i) ≤ c * v i ^ θ := by
    intro ⟨i, hi⟩
    simp only
    have hs0 : 0 ≤ s i := hT.trans (hsT i hi)
    rcases eq_or_lt_of_le (hv0 i) with h0 | hpos
    · rw [← h0, zero_mul, Real.zero_rpow hθ0.ne', mul_zero]
    · have hsplit : v i = v i ^ θ * v i ^ (1 - θ) := by
        rw [← Real.rpow_add hpos, add_sub_cancel, Real.rpow_one]
      have hpow : v i ^ (1 - θ) ≤ (K * Real.exp (-(R * s i) / Real.exp 1)) ^ (1 - θ) :=
        Real.rpow_le_rpow (hv0 i) (hpen i hi) h1θ.le
      have hexp : (K * Real.exp (-(R * s i) / Real.exp 1)) ^ (1 - θ) =
          K ^ (1 - θ) * Real.exp ((1 - θ) * (-(R * s i) / Real.exp 1)) := by
        rw [Real.mul_rpow hK (Real.exp_pos _).le, ← Real.exp_mul, mul_comm (1 - θ)]
      have hgain : (1 - θ) * (-(R * s i) / Real.exp 1) + x * s i ≤
          -((1 - θ) * R * T) / (2 * Real.exp 1) := by
        have h1 : x * s i ≤ (1 - θ) * R / (2 * Real.exp 1) * s i :=
          mul_le_mul_of_nonneg_right hxR hs0
        have h2 : (1 - θ) * R * T ≤ (1 - θ) * R * s i :=
          mul_le_mul_of_nonneg_left (hsT i hi) (mul_nonneg h1θ.le hR)
        have e1 : (1 - θ) * (-(R * s i) / Real.exp 1) =
            -(2 * ((1 - θ) * R * s i)) / (2 * Real.exp 1) := by field_simp
        have e2 : (1 - θ) * R / (2 * Real.exp 1) * s i = (1 - θ) * R * s i / (2 * Real.exp 1) := by
          ring
        rw [e1]
        rw [e2] at h1
        have h3 : -(2 * ((1 - θ) * R * s i)) / (2 * Real.exp 1) + (1 - θ) * R * s i /
            (2 * Real.exp 1) = -((1 - θ) * R * s i) / (2 * Real.exp 1) := by ring
        have h4 : -((1 - θ) * R * s i) / (2 * Real.exp 1) ≤ -((1 - θ) * R * T) / (2 * Real.exp 1) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        linarith
      calc v i * Real.exp (x * s i) = v i ^ θ * (v i ^ (1 - θ) * Real.exp (x * s i)) := by
            rw [show v i * Real.exp (x * s i) = (v i ^ θ * v i ^ (1 - θ)) * Real.exp (x * s i) by
              rw [← hsplit]]
            ring
        _ ≤ v i ^ θ * (K ^ (1 - θ) * Real.exp ((1 - θ) * (-(R * s i) / Real.exp 1)) *
              Real.exp (x * s i)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hv0 i) _)
            rw [← hexp]
            exact mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
        _ = v i ^ θ * (K ^ (1 - θ) *
              Real.exp ((1 - θ) * (-(R * s i) / Real.exp 1) + x * s i)) := by
            rw [Real.exp_add]; ring
        _ ≤ v i ^ θ * c := by
            rw [hc]
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr hgain) (Real.rpow_nonneg hK _)) (Real.rpow_nonneg (hv0 i) _)
        _ = c * v i ^ θ := mul_comm _ _
  have hsD : Summable fun i : ↥D => c * v i ^ θ := (hsumθ.subtype _).mul_left c
  have hsum : Summable fun i : ↥D => v i * Real.exp (x * s i) :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hv0 i) (Real.exp_pos _).le) hterm hsD
  calc ∑' i : ↥D, v i * Real.exp (x * s i) ≤ ∑' i : ↥D, c * v i ^ θ :=
        Summable.tsum_le_tsum hterm hsum hsD
    _ = c * ∑' i : ↥D, v i ^ θ := tsum_mul_left
    _ ≤ c * ∑' i, v i ^ θ := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        exact Summable.tsum_subtype_le (fun i => v i ^ θ) D (fun i => Real.rpow_nonneg (hv0 i) _)
          hsumθ
    _ = K ^ (1 - θ) * (∑' i, v i ^ θ) *
          Real.exp (-((1 - θ) * R * T) / (2 * Real.exp 1)) := by rw [hc]; ring

end GaloisForLFunctions.HTGeometry
