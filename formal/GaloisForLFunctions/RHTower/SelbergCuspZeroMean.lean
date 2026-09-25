import GaloisForLFunctions.RHTower.SelbergCuspConstantTerm
import GaloisForLFunctions.RHTower.EisensteinHyperbolicChart

open MeasureTheory UpperHalfPlane ModularGroup Set Complex
open scoped MatrixGroups Pointwise

/-!
# Zero mean of the non-constant parts over the cusps of the `Γ(N)` cell

The non-constant part is uniformly bounded, `|E^*_σ(u, z)| ≤ S₁ S₂ econst(Im z)` (`norm_Estarσ_le`, from the
product majorant of its Fourier–Kloosterman terms). For every height `y > 0` and every weight `g` invariant under
the right `T`-shift of cosets, `Σ_c g_c (∫_{-1/2}^{1/2} E_∞(R_c(x+iy), u) dx − CT_c(u, y)) = 0`
(`sum_weighted_row_mean_zero`): averaging over the shift (`avg_sum`) assembles the `N` width-one pieces of each cusp
into a full period, whose integral is `N · CT_c(u, y)`. This is the vanishing of the constant term of the truncated
Eisenstein series above the truncation height.
-/

namespace GaloisForLFunctions.RHTower.SelbergCuspZeroMean
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SarnakXuePretrace
  GaloisForLFunctions.RHTower.SelbergCellCosetShift GaloisForLFunctions.RHTower.SelbergCusppieceAveraging
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier GaloisForLFunctions.RHTower.SelbergCuspConstantTerm
  GaloisForLFunctions.RHTower.SelbergEisensteinStar GaloisForLFunctions.RHTower.SelbergPoincareKernel
open CongruenceSubgroup

variable (N : ℕ) [NeZero N]

/-- `S₁(σ) = Σ_{c≠0} |c|^{-2σ}`. -/
noncomputable def S1 (σ : ℝ) : ℝ := ∑' c : ℤ, if c = 0 then 0 else 1 * |(c : ℝ)| ^ (-(2 * σ))
/-- `S₂ = Σ_{n≠0} |n|^{-2}`. -/
noncomputable def S2 : ℝ := ∑' n : ℤ, if n = 0 then 0 else 1 * |(n : ℝ)| ^ (-(2 : ℝ))

/-- **Uniform bound for the non-constant part**: `|E^*_σ(u, z)| ≤ S₁ S₂ econst(Im z)`. -/
theorem norm_Estarσ_le (σ : SL(2, ℤ)) {u : ℂ} (hu : 1 / 2 < u.re) (z : ℍ) :
    ‖Estarσ N σ u z‖ ≤ S1 u.re * (S2 * econst N z.im u.re u.re ‖u‖) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have he : 0 ≤ econst N z.im u.re u.re ‖u‖ := by
    have := cst_nonneg u.re; have hy : 0 < z.im / N := div_pos z.im_pos hN
    unfold econst; positivity
  set f : ℤ → ℝ := fun c => if c = 0 then 0 else 1 * |(c : ℝ)| ^ (-(2 * u.re))
  set g : ℤ → ℝ := fun k => if k = 0 then 0 else econst N z.im u.re u.re ‖u‖ * |(k : ℝ)| ^ (-(2 : ℝ))
  have hf : Summable f := summable_ite_abs (by linarith) 1 zero_le_one
  have hg : Summable g := summable_ite_abs (by norm_num) _ he
  have hf0 : ∀ c, 0 ≤ f c := fun c => by simp only [f]; split_ifs <;> positivity
  have hg0 : ∀ k, 0 ≤ g k := fun k => by simp only [g]; split_ifs <;> positivity
  have hprod : Summable (fun p : ℤ × ℤ => f p.1 * g p.2) := Summable.mul_of_nonneg hf hg hf0 hg0
  have hb : ∀ p : ℤ × ℤ, ‖etermσ N σ u z p‖ ≤ f p.1 * g p.2 := fun p =>
    (norm_etermσ_le N σ z hu le_rfl le_rfl le_rfl p).trans (le_of_eq (by simp only [f, g, one_mul]))
  unfold Estarσ
  refine (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hprod)).trans ?_
  refine (Summable.tsum_le_tsum hb (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hprod) hprod).trans
    (le_of_eq ?_)
  have hfn : Summable (fun c => ‖f c‖) := hf.congr (fun c => (Real.norm_of_nonneg (hf0 c)).symm)
  have hgn : Summable (fun k => ‖g k‖) := hg.congr (fun k => (Real.norm_of_nonneg (hg0 k)).symm)
  rw [← tsum_mul_tsum_of_summable_norm hfn hgn]
  unfold S1 S2
  simp only [f, g]
  congr 1
  rw [← tsum_mul_right]
  apply tsum_congr; intro k
  split_ifs <;> ring

local notation "𝐄" => GaloisForLFunctions.RHTower.SelbergPoincare.poincare

omit [NeZero N] in
theorem continuous_pt_x {y : ℝ} (hy : 0 < y) : Continuous (fun x : ℝ => pt x y hy) := by
  have h : (fun x : ℝ => pt x y hy) = fun x => ofComplex (GaloisForLFunctions.RHTower.SelbergMaassMean.point x y) :=
    funext fun x => pt_eq x y hy
  rw [h]
  have hp : Continuous (fun x : ℝ => GaloisForLFunctions.RHTower.SelbergMaassMean.point x y) := by
    show Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I)
    fun_prop
  refine ofComplex.continuousOn.comp_continuous hp (fun x => ?_)
  have him : 0 < (GaloisForLFunctions.RHTower.SelbergMaassMean.point x y).im := by
    simpa [GaloisForLFunctions.RHTower.SelbergMaassMean.point] using hy
  exact ⟨⟨_, him⟩, Set.mem_univ _, rfl⟩

theorem continuous_E_row (c : Cosets N) {u : ℂ} (hu : 1 < u.re) {y : ℝ} (hy : 0 < y) :
    Continuous (fun x : ℝ => 𝐄 N 0 u ((Quotient.out c : PSL2Z) • pt x y hy)) :=
  (GaloisForLFunctions.RHTower.SelbergPoincareBounded.continuous_poincare N 0 hu).comp
    ((continuous_const_smul _).comp (continuous_pt_x hy))

theorem CT_iterate (c : Cosets N) {u : ℂ} (hu : 1 < u.re) {y : ℝ} (hy : 0 < y) (j : ℕ) :
    CT N ((sh N)^[j] c) u y = CT N c u y := by
  induction j generalizing c with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, ih, CT_sh N c hu hy]

/-- **Zero mean of the non-constant parts over the cusps.** For every `y > 0` and every shift-invariant weight,
`Σ_c g_c (∫_{-1/2}^{1/2} E_∞(R_c(x+iy), u) dx − CT_c(u, y)) = 0`. -/
theorem sum_weighted_row_mean_zero (g : Cosets N → ℂ) (hg : ∀ c, g (sh N c) = g c) {u : ℂ} (hu : 1 < u.re)
    {y : ℝ} (hy : 0 < y) :
    ∑ c, g c * ((∫ x in (-1 / 2 : ℝ)..(1 / 2), 𝐄 N 0 u ((Quotient.out c : PSL2Z) • pt x y hy)) - CT N c u y) = 0 := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hF : ∀ (γ : Gamma N) z, 𝐄 N 0 u ((γ : SL(2, ℤ)) • z) = 𝐄 N 0 u z :=
    fun γ z => GaloisForLFunctions.RHTower.SelbergPoincare.poincare_smul N 0 u z γ
  set A : Cosets N → ℂ := fun c => (∫ x in (-1 / 2 : ℝ)..(1 / 2), 𝐄 N 0 u ((Quotient.out c : PSL2Z) • pt x y hy)) -
    CT N c u y
  have hsum : ∀ c, ∑ j ∈ Finset.range N, A ((sh N)^[j] c) = 0 := by
    intro c
    simp only [A]
    rw [Finset.sum_sub_distrib, sum_shift_integral N hF c hy
      ((continuous_E_row N c hu hy).intervalIntegrable _ _)]
    simp_rw [CT_iterate N c hu hy]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, integral_eq_CT N c hu hy, sub_self]
  have h := avg_sum N A g hg
  simp_rw [hsum, mul_zero, Finset.sum_const_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hN0

end GaloisForLFunctions.RHTower.SelbergCuspZeroMean
