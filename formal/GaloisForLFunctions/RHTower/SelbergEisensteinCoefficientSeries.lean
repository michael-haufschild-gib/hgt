import GaloisForLFunctions.RHTower.CoprimeClassExact
import GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL
import GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier

open Complex LSeries
open scoped MatrixGroups LSeries.notation ArithmeticFunction.Moebius

/-!
# The Dirichlet series of the Fourier coefficients of `E_∞` at `σ∞`, continued to the critical line

`S_σ(0, n; c) = [c ≡ σ₁₀] Σ_{e | c} μ(e) [(e,N)=1] [M | n] M ψ((sgn c · n/M) σ₁₁ ē)`, `M = |c|/e` (`ksumσ_eq_class`).
Grouping `e` by its unit class `u` turns the row weight `m ↦ S_σ(0, n; ±m)` into `Σ_u (μχ_N δ_u) ⍟ g_±(u, ·)` with
`g_±(u, M) = [M | n][±uM ≡ σ₁₀] M ψ((±n/M) σ₁₁ u⁻¹)` supported on the divisors of `n` (`fE_eq_sum`), so for
`Re s > 1/2` and `n ≠ 0`:
`Σ_c |c|^{-2s} S_σ(0, n; c) = D_n(s) := Σ_u L_u(2s) Σ_{M | n} (g₊ + g₋)(u, M) M^{-2s}` (`tsum_ksumσ_eq_Dn`).
`D_n` is holomorphic wherever `2s ≠ 1` and no `L(2s, χ)` vanishes (`differentiableAt_Dn`), in particular on
`Re s ≥ 1/2`, `s ≠ 1/2` (`differentiableAt_Dn_of_half_le`), with `|D_n(s)| ≤ (Σ_u |L_u(2s)|) Σ_{M|n} 2M^{1-2Re s}`
(`norm_Dn_le`).
-/

namespace GaloisForLFunctions.RHTower.SelbergEisensteinCoefficientSeries
open GaloisForLFunctions.RHTower.SelbergEisensteinCusp GaloisForLFunctions.RHTower.SelbergPoincareFourier
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspCount GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier
  GaloisForLFunctions.RHTower.CoprimeClassRamanujan GaloisForLFunctions.RHTower.CoprimeClassExact
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspScattering GaloisForLFunctions.RHTower.TotientMulLSeries
  GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL GaloisForLFunctions.RHTower.TotientMulMoebius

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

/-- The residue `b = σ₁₁ mod N` as a natural number. -/
noncomputable abbrev bσ : ℕ := ((σ 1 1 : ℤ) : ZMod N).val

theorem ksumσ_eq_class {c : ℤ} (hc : c ≠ 0) (n : ℤ) :
    ksumσ N σ c n = if (c : ZMod N) = σ 1 0 then
      ∑ e ∈ c.natAbs.divisors, (μ e : ℂ) * classTerm N c.natAbs (bσ N σ) (c.sign * n) e else 0 := by
  classical
  unfold ksumσ
  split_ifs with hcl
  · have hbσ : ((bσ N σ : ℕ) : ZMod N) = ((σ 1 1 : ℤ) : ZMod N) := ZMod.natCast_zmod_val _
    have hmem : ∀ r : ℕ, (c, (r : ℤ)) ∈ rowMul σ '' adm N ↔ (r ≡ bσ N σ [MOD N] ∧ c.natAbs.Coprime r) := by
      intro r
      rw [mem_image_congr, Int.isCoprime_iff_nat_coprime, ← ZMod.natCast_eq_natCast_iff, hbσ]
      simp [hcl]
    have hsum : ∑ r ∈ Finset.range (c.natAbs * N), (rowMul σ '' adm N).indicator (kphase N 0 n) (c, (r : ℤ)) =
        ∑ r ∈ (Finset.range (c.natAbs * N)).filter (fun r => r ≡ bσ N σ [MOD N] ∧ c.natAbs.Coprime r),
          ph (c.sign * n) (c.natAbs * N) r := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _
      rw [Set.indicator_apply]
      simp only [hmem, kphase_eq_ph N hc n r]
    rw [hsum, class_sum_eq (Int.natAbs_pos.mpr hc) (coprime_class N σ hcl)]
  · exact Finset.sum_eq_zero (fun r _ => Set.indicator_of_notMem (fun h => hcl ((mem_image_congr N σ _).mp h).1) _)

/-- The divisor-side weight `M ↦ [M | n] [εuM ≡ σ₁₀] M ψ((εn/M) σ₁₁ u⁻¹)`. -/
noncomputable def gE (ε : ℤ) (n : ℤ) (u : (ZMod N)ˣ) (M : ℕ) : ℂ :=
  if M ≠ 0 ∧ (M : ℤ) ∣ n ∧ ((ε : ZMod N) * u * M = σ 1 0) then
    (M : ℂ) * ZMod.stdAddChar ((((ε * n) / M : ℤ) : ZMod N) * (bσ N σ : ZMod N) * ((u : ZMod N))⁻¹)
  else 0

/-- The row weight `m ↦ S_σ(0, n; εm)` on `ℕ`. -/
noncomputable def fE (ε : ℤ) (n : ℤ) (m : ℕ) : ℂ := if m = 0 then 0 else ksumσ N σ (ε * m) n

theorem fE_eq_sum (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (n : ℤ) (m : ℕ) (hm : m ≠ 0) :
    fE N σ ε n m = ∑ u : (ZMod N)ˣ, (muChiU N u ⍟ gE N σ ε n u) m := by
  classical
  have hc : ε * (m : ℤ) ≠ 0 := mul_ne_zero (by rcases hε with h | h <;> simp [h]) (by exact_mod_cast hm)
  have hsign : (ε * (m : ℤ)).sign = ε := by
    rcases hε with h | h <;> subst h <;> simp [Int.sign_natCast_of_ne_zero hm]
  have habs : (ε * (m : ℤ)).natAbs = m := by rcases hε with h | h <;> subst h <;> simp
  unfold fE
  rw [if_neg hm, ksumσ_eq_class N σ hc, hsign, habs]
  simp only [LSeries.convolution_def]
  rw [Finset.sum_comm, Nat.sum_divisorsAntidiagonal (fun e M => ∑ u : (ZMod N)ˣ, muChiU N u e * gE N σ ε n u M)]
  split_ifs with hcl
  · apply Finset.sum_congr rfl
    intro e he
    have hem : e ∣ m := Nat.dvd_of_mem_divisors he
    have hM0 : m / e ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hem)
      (Nat.pos_of_dvd_of_pos hem (Nat.pos_of_ne_zero hm))).ne'
    by_cases hco : e.Coprime N
    · set u0 := ZMod.unitOfCoprime e hco
      have hu0 : ((u0 : ZMod N)) = e := ZMod.coe_unitOfCoprime e hco
      have hiff : ∀ u : (ZMod N)ˣ, ((e : ZMod N) = u) ↔ u = u0 := by
        intro u; rw [← hu0]; constructor
        · intro h; exact Units.ext h.symm
        · intro h; rw [h]
      simp only [muChiU, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
      simp_rw [hiff]
      rw [Finset.sum_ite_eq' Finset.univ u0, if_pos (Finset.mem_univ _)]
      have hmu : muChi N e = (μ e : ℂ) := by
        simp [muChi, ArithmeticFunction.pmul_apply, chi, hco, (Nat.pos_of_dvd_of_pos hem (Nat.pos_of_ne_zero hm)).ne']
      rw [hmu]
      congr 1
      unfold classTerm gE
      have hcls : ((ε : ZMod N) * (u0 : ZMod N) * ((m / e : ℕ) : ZMod N) = σ 1 0) := by
        have hm' : ((m : ℕ) : ZMod N) = (e : ZMod N) * ((m / e : ℕ) : ZMod N) := by
          rw [← Nat.cast_mul, Nat.mul_div_cancel' hem]
        rw [hu0, ← hcl]
        push_cast; rw [hm']; ring
      by_cases hd : (((m / e : ℕ) : ℤ)) ∣ ε * n
      · have hd' : (((m / e : ℕ) : ℤ)) ∣ n := by
          rcases hε with h | h <;> subst h <;> simpa using hd
        rw [if_pos ⟨hco, hd⟩, if_pos ⟨hM0, hd', hcls⟩, hu0]
      · have hd' : ¬ (((m / e : ℕ) : ℤ)) ∣ n := fun h => hd (dvd_mul_of_dvd_right h _)
        rw [if_neg (fun h => hd h.2), if_neg (fun h => hd' h.2.1)]
    · have h0 : ∀ u : (ZMod N)ˣ, muChiU N u e = 0 := fun u => by
        simp [muChiU, muChi_eq_zero N hco]
      simp only [h0, zero_mul, Finset.sum_const_zero]
      unfold classTerm
      rw [if_neg (fun h => hco h.1), mul_zero]
  · symm
    apply Finset.sum_eq_zero
    intro e he
    have hem : e ∣ m := Nat.dvd_of_mem_divisors he
    apply Finset.sum_eq_zero
    intro u _
    unfold muChiU gE
    have hm' : ((m : ℕ) : ZMod N) = (e : ZMod N) * ((m / e : ℕ) : ZMod N) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hem]
    split_ifs with h1 h2
    · exfalso
      apply hcl
      rw [← h2.2.2, ← h1]
      push_cast; rw [hm']; ring
    all_goals simp

theorem gE_eq_zero_of_not_mem (ε : ℤ) {n : ℤ} (hn : n ≠ 0) (u : (ZMod N)ˣ) {M : ℕ} (hM : M ∉ n.natAbs.divisors) :
    gE N σ ε n u M = 0 := by
  unfold gE
  rw [if_neg]
  rintro ⟨h0, hd, _⟩
  exact hM (Nat.mem_divisors.mpr ⟨Int.natCast_dvd.mp hd, Int.natAbs_ne_zero.mpr hn⟩)

theorem summable_gE (ε : ℤ) {n : ℤ} (hn : n ≠ 0) (u : (ZMod N)ˣ) (w : ℂ) :
    LSeriesSummable (gE N σ ε n u) w := by
  unfold LSeriesSummable
  refine summable_of_ne_finset_zero (s := n.natAbs.divisors) (fun M hM => ?_)
  rw [LSeries.term_def]
  split_ifs
  · rfl
  · rw [gE_eq_zero_of_not_mem N σ ε hn u hM, zero_div]

theorem LSeries_gE (ε : ℤ) {n : ℤ} (hn : n ≠ 0) (u : (ZMod N)ˣ) (w : ℂ) :
    LSeries (gE N σ ε n u) w = ∑ M ∈ n.natAbs.divisors, gE N σ ε n u M / (M : ℂ) ^ w := by
  unfold LSeries
  rw [tsum_eq_sum (s := n.natAbs.divisors) (fun M hM => by
    rw [LSeries.term_def]; split_ifs
    · rfl
    · rw [gE_eq_zero_of_not_mem N σ ε hn u hM, zero_div])]
  apply Finset.sum_congr rfl
  intro M hM
  rw [LSeries.term_of_ne_zero (Nat.pos_of_mem_divisors hM).ne']

theorem norm_fE_le (ε : ℤ) (hε : ε = 1 ∨ ε = -1) {n : ℤ} (hn : n ≠ 0) (m : ℕ) :
    ‖fE N σ ε n m‖ ≤ (n.natAbs : ℝ) ^ 2 := by
  unfold fE
  split_ifs with hm
  · rw [norm_zero]; positivity
  · have hc : ε * (m : ℤ) ≠ 0 := mul_ne_zero (by rcases hε with h | h <;> simp [h]) (by exact_mod_cast hm)
    exact norm_ksumσ_le N σ hc hn

theorem summable_fE (ε : ℤ) (hε : ε = 1 ∨ ε = -1) {n : ℤ} (hn : n ≠ 0) {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fE N σ ε n) w :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) hw ⟨(n.natAbs : ℝ) ^ 2, fun m _ => by
    rw [sub_self, Real.rpow_zero, mul_one]; exact norm_fE_le N σ ε hε hn m⟩

theorem LSeries_fE (ε : ℤ) (hε : ε = 1 ∨ ε = -1) {n : ℤ} (hn : n ≠ 0) {w : ℂ} (hw : 1 < w.re) :
    LSeries (fE N σ ε n) w = ∑ u : (ZMod N)ˣ, LU N u w * ∑ M ∈ n.natAbs.divisors, gE N σ ε n u M / (M : ℂ) ^ w := by
  rw [LSeries_congr (g := ∑ u : (ZMod N)ˣ, (muChiU N u ⍟ gE N σ ε n u))
    (fun {m} hm => by rw [Finset.sum_apply]; exact fE_eq_sum N σ ε hε n m hm)]
  rw [LSeries_sum (fun u _ => LSeriesSummable.convolution (summable_muChiU N u hw) (summable_gE N σ ε hn u w))]
  apply Finset.sum_congr rfl
  intro u _
  rw [LSeries_convolution' (summable_muChiU N u hw) (summable_gE N σ ε hn u w), LSeries_muChiU_eq N hw,
    LSeries_gE N σ ε hn u w]

/-- **The continued Ramanujan–Dirichlet series** of the `n`-th Fourier coefficient at `σ∞`:
`D_n(s) = Σ_u L_u(2s) Σ_{M | n} (g₊ + g₋)(u, M) M^{-2s}`. -/
noncomputable def Dn (n : ℤ) (s : ℂ) : ℂ :=
  ∑ u : (ZMod N)ˣ, LU N u (2 * s) * ∑ M ∈ n.natAbs.divisors,
    (gE N σ 1 n u M + gE N σ (-1) n u M) / (M : ℂ) ^ (2 * s)

omit [NeZero N] in
theorem ksumσ_zero_left (n : ℤ) : ksumσ N σ 0 n = 0 := by simp [ksumσ]

/-- **`Σ_c |c|^{-2s} S_σ(0, n; c) = D_n(s)`** for `Re s > 1/2`, `n ≠ 0`. -/
theorem tsum_ksumσ_eq_Dn {n : ℤ} (hn : n ≠ 0) {s : ℂ} (hs : 1 / 2 < s.re) :
    ∑' c : ℤ, (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * ksumσ N σ c n = Dn N σ n s := by
  set F : ℤ → ℂ := fun c => (((c : ℝ) ^ 2 : ℝ) : ℂ) ^ (-s) * ksumσ N σ c n
  have hw : 1 < (2 * s).re := by simp; linarith
  have hF : Summable F := by
    refine Summable.of_norm_bounded ((Real.summable_abs_int_rpow (b := 2 * s.re) (by linarith)).mul_right
      ((n.natAbs : ℝ) ^ 2)) (fun c => ?_)
    by_cases hc : c = 0
    · subst hc; simp only [F, ksumσ_zero_left, mul_zero, norm_zero]; positivity
    simp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_nonneg (by positivity) (by simp; linarith)]
    have hcsq : ((c : ℝ) ^ 2) ^ (-s).re = |(c : ℝ)| ^ (-(2 * s.re)) := by
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]; simp
    rw [hcsq]
    exact mul_le_mul_of_nonneg_left (norm_ksumσ_le N σ hc hn) (by positivity)
  have h := hF.hasSum.nat_add_neg
  have hF0 : F 0 = 0 := by simp [F, ksumσ_zero_left]
  rw [hF0, add_zero] at h
  have hterm : ∀ m : ℕ, F m + F (-m) = LSeries.term (fE N σ 1 n) (2 * s) m + LSeries.term (fE N σ (-1) n) (2 * s) m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [F, ksumσ_zero_left]
    rw [LSeries.term_of_ne_zero hm.ne', LSeries.term_of_ne_zero hm.ne']
    simp only [F, fE, if_neg hm.ne', one_mul, neg_one_mul, Int.cast_neg, Int.cast_natCast, neg_sq]
    rw [sq_cpow_neg s hm]
    ring
  have h2 := (h.congr_fun (fun m => (hterm m).symm))
  rw [← h2.tsum_eq, Summable.tsum_add (summable_fE N σ 1 (Or.inl rfl) hn hw) (summable_fE N σ (-1) (Or.inr rfl) hn hw)]
  change LSeries (fE N σ 1 n) (2 * s) + LSeries (fE N σ (-1) n) (2 * s) = _
  rw [LSeries_fE N σ 1 (Or.inl rfl) hn hw, LSeries_fE N σ (-1) (Or.inr rfl) hn hw, ← Finset.sum_add_distrib, Dn]
  apply Finset.sum_congr rfl
  intro u _
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 2
  funext M
  ring

theorem differentiableAt_LU_of (u : (ZMod N)ˣ) {w : ℂ} (hw1 : w ≠ 1)
    (hne : ∀ χ : DirichletCharacter ℂ N, DirichletCharacter.LFunction χ w ≠ 0) :
    DifferentiableAt ℂ (LU N u) w := by
  unfold LU
  refine DifferentiableAt.const_mul ?_ _
  have : (fun w => ∑ χ : DirichletCharacter ℂ N, χ ((u : ZMod N)⁻¹) * (DirichletCharacter.LFunction χ w)⁻¹) =
      ∑ χ : DirichletCharacter ℂ N, fun w => χ ((u : ZMod N)⁻¹) * (DirichletCharacter.LFunction χ w)⁻¹ := by
    funext w; simp [Finset.sum_apply]
  rw [this]
  exact DifferentiableAt.sum (fun χ _ =>
    ((DirichletCharacter.differentiableAt_LFunction χ w (Or.inl hw1)).inv (hne χ)).const_mul _)

/-- **Holomorphy of `D_n`** at every `s` with `2s ≠ 1` where no `L(·, χ)` vanishes at `2s`. -/
theorem differentiableAt_Dn (n : ℤ) {s : ℂ} (hs1 : 2 * s ≠ 1)
    (hne : ∀ χ : DirichletCharacter ℂ N, DirichletCharacter.LFunction χ (2 * s) ≠ 0) :
    DifferentiableAt ℂ (Dn N σ n) s := by
  unfold Dn
  have e : (fun s : ℂ => ∑ u : (ZMod N)ˣ, LU N u (2 * s) * ∑ M ∈ n.natAbs.divisors,
      (gE N σ 1 n u M + gE N σ (-1) n u M) / (M : ℂ) ^ (2 * s)) =
      ∑ u : (ZMod N)ˣ, fun s : ℂ => LU N u (2 * s) * ∑ M ∈ n.natAbs.divisors,
        (gE N σ 1 n u M + gE N σ (-1) n u M) / (M : ℂ) ^ (2 * s) := by
    funext s; simp [Finset.sum_apply]
  rw [e]
  refine DifferentiableAt.sum (fun u _ => ?_)
  refine ((differentiableAt_LU_of N u hs1 hne).comp s (differentiableAt_id.const_mul 2)).mul ?_
  have e2 : (fun s : ℂ => ∑ M ∈ n.natAbs.divisors, (gE N σ 1 n u M + gE N σ (-1) n u M) / (M : ℂ) ^ (2 * s)) =
      ∑ M ∈ n.natAbs.divisors, fun s : ℂ => (gE N σ 1 n u M + gE N σ (-1) n u M) / (M : ℂ) ^ (2 * s) := by
    funext s; simp [Finset.sum_apply]
  rw [e2]
  refine DifferentiableAt.sum (fun M hM => ?_)
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hM).ne'
  exact (differentiableAt_const _).div ((differentiableAt_id.const_mul 2).const_cpow (Or.inl hM0))
    (by rw [Ne, cpow_eq_zero_iff]; tauto)

/-- On the closed half-plane `Re s ≥ 1/2` minus `s = 1/2`, `D_n` is holomorphic. -/
theorem differentiableAt_Dn_of_half_le (n : ℤ) {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1 / 2) :
    DifferentiableAt ℂ (Dn N σ n) s := by
  have h2 : 2 * s ≠ 1 := fun h => hs1 (by linear_combination h / 2)
  exact differentiableAt_Dn N σ n h2 (fun χ => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr h2)
    (by simp; linarith))

theorem norm_gE_le (ε : ℤ) (n : ℤ) (u : (ZMod N)ˣ) (M : ℕ) : ‖gE N σ ε n u M‖ ≤ M := by
  unfold gE
  split_ifs
  · rw [norm_mul, Complex.norm_natCast, AddChar.norm_apply, mul_one]
  · rw [norm_zero]; positivity

/-- **Bound for `D_n`**: `|D_n(s)| ≤ (Σ_u |L_u(2s)|) · Σ_{M | n} 2M^{1-2Re s}`. -/
theorem norm_Dn_le (n : ℤ) (s : ℂ) :
    ‖Dn N σ n s‖ ≤ (∑ u : (ZMod N)ˣ, ‖LU N u (2 * s)‖) *
      ∑ M ∈ n.natAbs.divisors, 2 * (M : ℝ) ^ (1 - 2 * s.re) := by
  unfold Dn
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun u _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun M hM => ?_))
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_mem_divisors hM
  rw [norm_div, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_mem_divisors hM)]
  have hre : (2 * s).re = 2 * s.re := by simp
  rw [hre, div_le_iff₀ (Real.rpow_pos_of_pos hMpos _)]
  calc ‖gE N σ 1 n u M + gE N σ (-1) n u M‖ ≤ M + M :=
        (norm_add_le _ _).trans (add_le_add (norm_gE_le N σ 1 n u M) (norm_gE_le N σ (-1) n u M))
    _ = 2 * (M : ℝ) ^ (1 - 2 * s.re) * (M : ℝ) ^ (2 * s.re) := by
        rw [mul_assoc, ← Real.rpow_add hMpos]; simp; ring

end GaloisForLFunctions.RHTower.SelbergEisensteinCoefficientSeries
