import GaloisForLFunctions.RHTower.BeurlingDeletionPerron
import GaloisForLFunctions.RHTower.BeurlingDeletionPrimeAsymptotics
import GaloisForLFunctions.HTGeometry.AbelConstantContinuation
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# Prime-deletion Beurling systems: `[α, β]`-systems with `β < 1/2` under RH

A discrete Beurling system is an `[α, β]`-system when `ψ(x) = x + O(x^{α+ε})` and
`N(x) = a x + O(x^{β+ε})` (`a > 0`) for every `ε > 0`, and neither exponent can be lowered
(`BeurlingSystem.IsAlphaBetaSystem`).

**Assembly** (`isAlphaBetaSystem_of_count`).  Let `1/2 < α < 1`, `S` a deletion set with the
discrepancy bound (R), and suppose the `S`-free integers satisfy `N'(x) = a' x + O(x^γ)` with
`γ < β`, `α/2 < β < 1/2`.  Then `(ℙ ∖ S) ∪ ℙ^{1/β}` is an `[α, β]`-system:

* integers: `N(x) = a Z₁ x + Z_β x^β + O(x^{β/(1+β−γ)})` (hyperbola), with
  `(β − 1) Z_β = H(β) = ζ_u(β) E(β) (β − α)/ζ_u(β + 1 − α) ≠ 0` (continuation of the Abel
  constant), `a = H(1) > 0` and `Z₁ ≥ 1/2`;
* primes: `ψ_B(x) − x = O(x^{α+ε})` and `≠ O(x^{α−ε})` (`BeurlingDeletionPrimeAsymptotics`).

**The Perron region** (`exists_isAlphaBetaSystem_of_perron`).  Under RH, for `1/2 < α < 1` and
`1/(3 − α) < β < 1/2` there is an `[α, β]`-system: Perron's formula gives
`N'(x) = a' x + O(x^{1/(3−α)+η})` (`exists_norm_count_sub_le`).
-/

open Complex Finset Filter Asymptotics

noncomputable section

namespace RHTower

namespace BeurlingSystem

/-- **An `[α, β]`-system**: discrete, `ψ(x) = x + O(x^{α+ε})` and `N(x) = a x + O(x^{β+ε})` with
`a > 0` for every `ε > 0`, and neither exponent can be lowered. -/
def IsAlphaBetaSystem (B : BeurlingSystem) (α β : ℝ) : Prop :=
  B.IsDiscrete ∧
    (∀ ε > 0, (fun x => B.chebyshevPsi x - x) =O[atTop] fun x => x ^ (α + ε)) ∧
    (∀ ε > 0, ¬ (fun x => B.chebyshevPsi x - x) =O[atTop] fun x => x ^ (α - ε)) ∧
    ∃ a : ℝ, 0 < a ∧
      (∀ ε > 0, (fun x => (B.countBall x : ℝ) - a * x) =O[atTop] fun x => x ^ (β + ε)) ∧
      (∀ ε > 0, ¬ (fun x => (B.countBall x : ℝ) - a * x) =O[atTop] fun x => x ^ (β - ε))

end BeurlingSystem

namespace BeurlingDeletion

open GaloisForLFunctions.HTGeometry.PowerHyperbola

namespace DeletionData

variable {α : ℝ} (D : DeletionData α)

theorem sFreeInd_eq (n : ℕ) : D.sFreeInd n = ((sFreeR D.S n : ℝ) : ℂ) := by
  classical
  unfold sFreeInd sFreeR
  by_cases h : D.sFree n
  · have h' : SFree D.S n := h
    simp [h, h']
  · have h' : ¬ SFree D.S n := h
    simp [h, h']

theorem count_eq (X : ℝ) : D.count X = ((countFn (sFreeR D.S) X : ℝ) : ℂ) := by
  unfold count countFn
  have hI : Finset.Iic ⌊X⌋₊ = Finset.Icc 0 ⌊X⌋₊ := by ext n; simp
  rw [hI, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun n _ => D.sFreeInd_eq n

theorem perronNum_ne_zero (hRH : RiemannHypothesis) (hα : α < 1) {s : ℂ} (hs : α / 2 < s.re)
    (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) (hsα : s ≠ (α : ℂ)) : D.perronNum s ≠ 0 := by
  unfold perronNum
  refine mul_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) ?_
  · rw [zetaResidueUnit_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) hζ
  · unfold qFactor
    exact div_ne_zero (sub_ne_zero.mpr hsα) (zetaResidueUnit_shift_ne_zero hRH hα hs)

theorem perronNum_one_ne_zero (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1) :
    D.perronNum 1 ≠ 0 := by
  unfold perronNum
  rw [zetaResidueUnit_one, one_mul]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  unfold qFactor
  refine div_ne_zero ?_ (zetaResidueUnit_shift_ne_zero hRH hα (by simp; linarith))
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

end DeletionData

/-- `Z₁ = Σ_m m^{−p} ≥ 1/2` for `p > 1`. -/
theorem abelConst_oneSeq_ge {p : ℝ} (hp : 1 < p) : 1 / 2 ≤ abelConst oneSeq 1 p := by
  have hA1 : ∀ t : ℝ, 1 ≤ t → |countFn oneSeq t - 1 * t| ≤ 1 * t ^ (0 : ℝ) :=
    fun t ht => abs_countFn_oneSeq_sub_le ht
  have h := abs_sum_rpow_mul_sub_le oneSeq oneSeq_zero (a := 1) (C := 1) (γ := 0) (p := p)
    (by linarith) (by linarith) (ne_of_gt hp) hA1 (Y := 4) (by norm_num)
  rw [← sum_Icc_one_rpow_eq] at h
  have hfl : ⌊(4 : ℝ)⌋₊ = 4 := by norm_num
  rw [hfl] at h
  have hS : 1 ≤ ∑ m ∈ Finset.Icc (1 : ℕ) 4, ((m : ℕ) : ℝ) ^ (-p) := by
    have := Finset.single_le_sum (f := fun m : ℕ => ((m : ℕ) : ℝ) ^ (-p))
      (fun m _ => by positivity) (show (1 : ℕ) ∈ Finset.Icc (1 : ℕ) 4 by simp)
    simpa using this
  have hneg : 1 * (4 : ℝ) ^ (1 - p) / (1 - p) ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have hsmall : 1 * (1 + p / (p - 0)) * (4 : ℝ) ^ (0 - p) ≤ 1 / 2 := by
    have h4p : (4 : ℝ) ^ (0 - p) ≤ 1 / 4 := by
      calc (4 : ℝ) ^ (0 - p) ≤ 4 ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 4 := by rw [Real.rpow_neg_one]; norm_num
    have hpp : 1 * (1 + p / (p - 0)) = 2 := by
      rw [sub_zero, div_self (by linarith)]; norm_num
    rw [hpp]
    linarith
  have := (abs_le.mp h).2
  linarith

/-- A secondary term `Z x^β` with `Z ≠ 0` and remainder `O(x^e)`, `e < β`, gives
`f = O(x^{β+ε})` and `f ≠ O(x^{β−ε})`. -/
theorem isBigO_not_isBigO_of_expansion {f : ℝ → ℝ} {Z K β e : ℝ} (hZ : Z ≠ 0) (he : e < β)
    (hf : ∀ x : ℝ, 1 ≤ x → |f x - Z * x ^ β| ≤ K * x ^ e) :
    (∀ ε > 0, f =O[atTop] fun x => x ^ (β + ε)) ∧
      ∀ ε > 0, ¬ f =O[atTop] fun x => x ^ (β - ε) := by
  constructor
  · intro ε hε
    refine IsBigO.of_bound (|Z| + |K|) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have h1 : x ^ β ≤ x ^ (β + ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have h2 : x ^ e ≤ x ^ (β + ε) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hb := hf x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    have hpos : 0 < x ^ β := Real.rpow_pos_of_pos hx0 _
    have hpos' : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
    calc |f x| ≤ |f x - Z * x ^ β| + |Z * x ^ β| := by
          have := abs_sub_abs_le_abs_sub (f x) (Z * x ^ β); linarith
      _ ≤ |K| * x ^ e + |Z| * x ^ β := by
          rw [abs_mul, abs_of_pos hpos]
          have : K * x ^ e ≤ |K| * x ^ e := mul_le_mul_of_nonneg_right (le_abs_self K) hpos'.le
          linarith
      _ ≤ |K| * x ^ (β + ε) + |Z| * x ^ (β + ε) := by gcongr
      _ = (|Z| + |K|) * x ^ (β + ε) := by ring
  · intro ε hε h
    obtain ⟨K', hK'⟩ := h.bound
    set r : ℝ := min ε (β - e) with hr
    have hr0 : 0 < r := lt_min hε (by linarith)
    have hZ0 : 0 < |Z| := abs_pos.mpr hZ
    obtain ⟨x, ⟨hx1, hx⟩, hx2⟩ := ((eventually_ge_atTop (1 : ℝ)).and hK').and
      (BeurlingDeletion.eventually_const_mul_rpow_le ((|K'| + |K| + 1) / |Z|) (a := β - r) (b := β)
        (by linarith)) |>.exists
    have hx0 : 0 < x := by linarith
    have hmono : ∀ {a b : ℝ}, a ≤ b → x ^ a ≤ x ^ b := fun h =>
      Real.rpow_le_rpow_of_exponent_le hx1 h
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hx
    have hb := hf x hx1
    have hpos : 0 < x ^ (β - r) := Real.rpow_pos_of_pos hx0 _
    have h1 : |Z| * x ^ β ≤ |K'| * x ^ (β - r) + |K| * x ^ (β - r) := by
      have hZx : |Z * x ^ β| = |Z| * x ^ β := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
      have ha : |Z * x ^ β| ≤ |f x| + |f x - Z * x ^ β| := by
        have := abs_sub_abs_le_abs_sub (Z * x ^ β) (f x)
        rw [abs_sub_comm (Z * x ^ β)] at this; linarith
      have hc : K' * x ^ (β - ε) ≤ |K'| * x ^ (β - r) :=
        (mul_le_mul_of_nonneg_right (le_abs_self K') (by positivity)).trans
          (mul_le_mul_of_nonneg_left (hmono (by linarith [min_le_left ε (β - e)])) (abs_nonneg _))
      have hd : K * x ^ e ≤ |K| * x ^ (β - r) :=
        (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)).trans
          (mul_le_mul_of_nonneg_left (hmono (by linarith [min_le_right ε (β - e)]))
            (abs_nonneg _))
      linarith
    have h2 : (|K'| + |K| + 1) * x ^ (β - r) ≤ |Z| * x ^ β := by
      have := mul_le_mul_of_nonneg_left hx2 hZ0.le
      rw [← mul_assoc, mul_div_cancel₀ _ hZ0.ne'] at this
      linarith
    nlinarith

namespace DeletionData

variable {α : ℝ} (D : DeletionData α)

/-- The real count `A(t) = #{n ≤ t : n S-free}` inherits the bound on the complex count. -/
theorem abs_countFn_sub_le {C γ : ℝ}
    (hcount : ∀ X : ℝ, 1 ≤ X → ‖D.count X - D.density * X‖ ≤ C * X ^ γ) (t : ℝ) (ht : 1 ≤ t) :
    |countFn (sFreeR D.S) t - D.density.re * t| ≤ C * t ^ γ := by
  refine le_trans ?_ (hcount t ht)
  have : countFn (sFreeR D.S) t - D.density.re * t = (D.count t - D.density * t).re := by
    rw [D.count_eq]; simp
  rw [this]
  exact Complex.abs_re_le_norm _

/-- The density of the `S`-free integers is positive. -/
theorem density_re_pos (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1) {C γ : ℝ} (hγ1 : γ < 1)
    (hcount : ∀ X : ℝ, 1 ≤ X → ‖D.count X - D.density * X‖ ≤ C * X ^ γ) :
    0 < D.density.re ∧ D.density = (D.density.re : ℂ) := by
  have hA := D.abs_countFn_sub_le hcount
  have hLS : ∀ s : ℂ, 1 < s.re → D.perronNum s / (s - 1) =
      LSeries (fun n => ((sFreeR D.S n : ℝ) : ℂ)) s := by
    intro s hs
    rw [D.perronNum_div_eq_LSeries hα0 hα hs]
    congr 1; funext n; exact D.sFreeInd_eq n
  have hdens := eq_density (sFreeR D.S) (sFreeR_zero D.S) (abs_sFreeR_le D.S) hγ1 hA
    (a₀ := α / 2) (by linarith) (D.differentiableOn_perronNum hRH hα0 hα) hLS
  have hreal : D.density = (D.density.re : ℂ) := hdens
  refine ⟨?_, hreal⟩
  have hne : D.density.re ≠ 0 := by
    intro h
    apply D.perronNum_one_ne_zero hRH hα0 hα
    rw [← density, hreal, h, Complex.ofReal_zero]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exfalso
    have hC : 0 ≤ C := by
      have := (abs_nonneg _).trans (hA 1 le_rfl); simpa using this
    set a := D.density.re
    set X : ℝ := max 1 (((C + 1) / (-a)) ^ (1 / (1 - γ))) with hX
    have hX1 : 1 ≤ X := le_max_left _ _
    have hX0 : 0 < X := by linarith
    have hbound := hA X hX1
    have hA0 : 0 ≤ countFn (sFreeR D.S) X := by
      unfold countFn; exact Finset.sum_nonneg fun n _ => sFreeR_nonneg D.S n
    have h1 : -a * X ≤ C * X ^ γ := by
      have := (abs_le.mp hbound).2; linarith
    have hXγ : X ^ (1 - γ) * X ^ γ = X := by rw [← Real.rpow_add hX0]; simp
    have h2 : (C + 1) / (-a) ≤ X ^ (1 - γ) := by
      have hq : 0 ≤ (C + 1) / (-a) := div_nonneg (by linarith) (by linarith)
      have hb : ((C + 1) / (-a)) ^ (1 / (1 - γ)) ≤ X := le_max_right _ _
      have := Real.rpow_le_rpow (Real.rpow_nonneg hq _) hb (by linarith : (0 : ℝ) ≤ 1 - γ)
      rwa [← Real.rpow_mul hq, one_div, inv_mul_cancel₀ (by linarith),
        Real.rpow_one] at this
    have h3 : C + 1 ≤ -a * X ^ (1 - γ) := by
      rw [div_le_iff₀ (by linarith)] at h2; linarith
    have hpos : 0 < X ^ γ := Real.rpow_pos_of_pos hX0 _
    have h4 : (C + 1) * X ^ γ ≤ -a * X := by
      calc (C + 1) * X ^ γ ≤ (-a * X ^ (1 - γ)) * X ^ γ := by gcongr
        _ = -a * X := by rw [mul_assoc, hXγ]
    nlinarith
  · exact hpos

/-- The secondary coefficient `Z_β` is nonzero. -/
theorem abelConst_ne_zero (hRH : RiemannHypothesis) (hα0 : 0 < α) (hα : α < 1) {C γ β : ℝ}
    (hγ1 : γ < 1) (hcount : ∀ X : ℝ, 1 ≤ X → ‖D.count X - D.density * X‖ ≤ C * X ^ γ)
    (hγβ : γ < β) (hαβ : α / 2 < β) (hβα : β < α) :
    abelConst (sFreeR D.S) D.density.re β ≠ 0 := by
  have hA := D.abs_countFn_sub_le hcount
  have hLS : ∀ s : ℂ, 1 < s.re → D.perronNum s / (s - 1) =
      LSeries (fun n => ((sFreeR D.S n : ℝ) : ℂ)) s := by
    intro s hs
    rw [D.perronNum_div_eq_LSeries hα0 hα hs]
    congr 1; funext n; exact D.sFreeInd_eq n
  have hβ1 : β < 1 := by linarith
  have hβ0 : 0 < β := by linarith
  have h := mul_abelConst_eq (sFreeR D.S) (sFreeR_zero D.S) (abs_sFreeR_le D.S) hγ1 hA
    (a₀ := α / 2) (D.differentiableOn_perronNum hRH hα0 hα) hLS hγβ hαβ (ne_of_lt hβ1)
  intro hZ
  rw [hZ, Complex.ofReal_zero, mul_zero] at h
  refine D.perronNum_ne_zero hRH hα (s := (β : ℂ)) (by simpa using hαβ) ?_ ?_ ?_ h.symm
  · intro h1; have := congrArg Complex.re h1; simp at this; linarith
  · exact riemannZeta_ne_zero_of_ofReal_mem_Ioo hβ0 hβ1
  · intro h1; have := congrArg Complex.re h1; simp at this; linarith

end DeletionData

/-- **Assembly.**  If the `S`-free integers satisfy `N'(x) = a' x + O(x^γ)` with `γ < β`, then the
deletion system `(ℙ ∖ S) ∪ ℙ^{1/β}` is an `[α, β]`-system. -/
theorem isAlphaBetaSystem_of_count (hRH : RiemannHypothesis) {α β γ : ℝ} (hα1 : 1 / 2 < α)
    (hα : α < 1) (D : DeletionData α) (hβ0 : 0 < β) (hβ1 : β < 1 / 2) (hαβ : α / 2 < β)
    (hγ0 : 0 < γ) (hγβ : γ < β)
    (hcount : ∃ C, ∀ X : ℝ, 1 ≤ X → ‖D.count X - D.density * X‖ ≤ C * X ^ γ) :
    (deletionSystem D.S β hβ0).IsAlphaBetaSystem α β := by
  obtain ⟨C, hC⟩ := hcount
  have hα0 : 0 < α := by linarith
  have hγ1 : γ < 1 := by linarith
  have hβα : β < α := by linarith
  have hA := D.abs_countFn_sub_le hC
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg _).trans (hA 1 le_rfl); simpa using this
  obtain ⟨hapos, -⟩ := D.density_re_pos hRH hα0 hα hγ1 hC
  have hZ := D.abelConst_ne_zero hRH hα0 hα hγ1 hC hγβ hαβ hβα
  obtain ⟨K, hK⟩ := abs_hyperbolaCount_sub_le (sFreeR D.S) (sFreeR_zero D.S) (abs_sFreeR_le D.S)
    hγ0 hγβ (by linarith) hC0 hA
  have hZ₁ := abelConst_oneSeq_ge (p := 1 / β) (by rw [lt_div_iff₀ hβ0]; linarith)
  set a := D.density.re
  set Z₁ := abelConst oneSeq 1 (1 / β)
  set Z := abelConst (sFreeR D.S) a β
  have hexp : β / (1 + β - γ) < β := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  have hN : ∀ x : ℝ, 1 ≤ x →
      |((deletionSystem D.S β hβ0).countBall x : ℝ) - a * Z₁ * x - Z * x ^ β| ≤
        K * x ^ (β / (1 + β - γ)) := by
    intro x hx
    rw [countBall_eq_hyperbolaCount D.S hβ0 (by linarith)]
    exact hK x hx
  have hN' : ∀ x : ℝ, 1 ≤ x →
      |(((deletionSystem D.S β hβ0).countBall x : ℝ) - a * Z₁ * x) - Z * x ^ β| ≤
        K * x ^ (β / (1 + β - γ)) := hN
  obtain ⟨hNup, hNlow⟩ := isBigO_not_isBigO_of_expansion hZ hexp hN'
  refine ⟨isDiscrete_deletionSystem D.S hβ0, fun ε hε => isBigO_chebyshevPsi_sub hRH hα1 hα.le D
    hβ0 hβα hε, fun ε hε => not_isBigO_chebyshevPsi_sub hRH hα1 hα.le D hβ0 hβα hε, a * Z₁,
    by positivity, hNup, hNlow⟩

/-- **The Perron region.**  Under RH, for `1/2 < α < 1` and `1/(3 − α) < β < 1/2` there is an
`[α, β]`-system. -/
theorem exists_isAlphaBetaSystem_of_perron (hRH : RiemannHypothesis) {α β : ℝ} (hα1 : 1 / 2 < α)
    (hα : α < 1) (hβ0 : 1 / (3 - α) < β) (hβ1 : β < 1 / 2) :
    ∃ B : BeurlingSystem, B.IsAlphaBetaSystem α β := by
  have hα0 : 0 < α := by linarith
  obtain ⟨D⟩ := exists_deletionData hα0 hα
  have h3 : 0 < 3 - α := by linarith
  have hthr : 0 < 1 / (3 - α) := by positivity
  set γ : ℝ := (1 / (3 - α) + β) / 2 with hγ
  have hβpos : 0 < β := by linarith
  have hαβ : α / 2 < β := by
    have : α / 2 < 1 / (3 - α) := by
      rw [lt_div_iff₀ h3]; nlinarith
    linarith
  obtain ⟨C, hC⟩ := D.exists_norm_count_sub_le hRH hα0 hα (η := γ - 1 / (3 - α)) (by linarith)
  refine ⟨deletionSystem D.S β hβpos, isAlphaBetaSystem_of_count hRH hα1 hα D hβpos hβ1 hαβ
    (by linarith) (by linarith) ⟨C, fun X hX => ?_⟩⟩
  have := hC X hX
  rwa [show 1 / (3 - α) + (γ - 1 / (3 - α)) = γ by ring] at this

end BeurlingDeletion

end RHTower
