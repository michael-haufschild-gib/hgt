import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import GaloisForLFunctions.RHTower.MertensAbelAssembly
import GaloisForLFunctions.RHTower.MertensTailConstant
import GaloisForLFunctions.RHTower.DirichletAbelTail
import GaloisForLFunctions.RHTower.DirichletIncrementDominated
import GaloisForLFunctions.RHTower.HarmonicPrimitiveMertensReduction
import GaloisForLFunctions.RHTower.HarmonicPrimitiveMassAdjoint

/-!
# Mertens' second theorem and the limit of the harmonic primitive

The source `a(n) = Λ(n) − 1` has summatory function `ψ(N) − N`, so a single error sequence
governs both sides of the comparison between the harmonic weight and the Dirichlet weight.

On the harmonic side, summation by parts gives

`∑_{n ≤ N} Λ(n)/n − log N → γ + T`,   `T = ∑_k (ψ(k+1) − (k+1))(1/(k+1) − 1/(k+2))`.

On the Dirichlet side, the same summation by parts represents `L(Λ, s) − ζ(s)` by the Abel tail of
the *same* error sequence, and letting `s → 1⁺` under the dominating weight `|ψ(m) − m|/m²`
evaluates that tail at `T`.  Since both poles cancel, `L(Λ, s) − ζ(s) → −2γ`, so `T = −2γ` and

`∑_{n ≤ N} Λ(n)/n − log N → −γ`.

Feeding this into the harmonic-primitive reduction gives the limit of the primitive itself,
`J_N → −2γ`.
-/

open Filter Topology ArithmeticFunction

namespace RHTower

noncomputable section

/-! ## The error sequence -/

/-- The Chebyshev error at `k + 1`. -/
def psiError (k : ℕ) : ℝ := Chebyshev.psi ((k : ℝ) + 1) - ((k : ℝ) + 1)

/-- A sum over `Icc 1 N` is the shifted sum over `range N`. -/
theorem sum_Icc_eq_sum_range_shift {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ i ∈ Finset.range N, f (i + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- Chebyshev's `ψ` at a natural point is the shifted von Mangoldt partial sum. -/
theorem psi_natCast_eq_sum_range (n : ℕ) :
    Chebyshev.psi (n : ℝ) = ∑ i ∈ Finset.range n, (vonMangoldt (i + 1) : ℝ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, ← Nat.range_succ_eq_Icc_zero,
    Finset.sum_range_succ']
  simp

theorem psiError_eq (k : ℕ) :
    psiError k = (∑ i ∈ Finset.range (k + 1), (vonMangoldt (i + 1) : ℝ)) - ((k : ℝ) + 1) := by
  rw [psiError]
  congr 1
  rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, psi_natCast_eq_sum_range]

theorem summable_absPsiError_weight :
    Summable fun k : ℕ => |psiError k| * (2 / ((k : ℝ) + 1) ^ 2) := by
  simpa only [psiError] using summable_psi_error_weight

/-- The harmonic increment is at most twice the inverse square. -/
theorem abs_harmonicIncrement_le (k : ℕ) :
    |1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)| ≤ 2 / ((k : ℝ) + 1) ^ 2 := by
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hval : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)
      = 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) := by
    rw [hval]
    positivity
  rw [abs_of_nonneg hnn, hval, div_le_div_iff₀ (by positivity) (by positivity)]
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith [sq_nonneg ((k : ℝ) + 1)]

theorem summable_psiError_increment :
    Summable fun k : ℕ => psiError k * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2)) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    summable_absPsiError_weight)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_harmonicIncrement_le k) (abs_nonneg _)

/-- The Abel tail constant of the Chebyshev error. -/
def mertensAbelTail : ℝ :=
  ∑' k : ℕ, psiError k * (1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2))

/-! ## The harmonic side -/

theorem tendsto_psi_natCast_div :
    Tendsto (fun n : ℕ => Chebyshev.psi (n : ℝ) / (n : ℝ)) atTop (𝓝 1) :=
  tendsto_psi_div_self.comp tendsto_natCast_atTop_atTop

/-- **Summation by parts against the harmonic weight.** -/
theorem tendsto_vonMangoldt_harmonicWeighted :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), (vonMangoldt (i + 1) : ℝ) / ((i : ℝ) + 1))
        - Real.log ((n : ℝ) + 1)) atTop
      (𝓝 (Real.eulerMascheroniConstant + mertensAbelTail)) := by
  refine tendsto_abelPartialSum_sub_log (c := fun i => (vonMangoldt (i + 1) : ℝ)) ?_ ?_
  · exact tendsto_psi_natCast_div.congr fun n => by rw [psi_natCast_eq_sum_range]
  · refine summable_psiError_increment.hasSum.tendsto_sum_nat.congr fun n => ?_
    exact Finset.sum_congr rfl fun k _ => by rw [psiError_eq]

/-! ## The Dirichlet side -/

/-- The coefficient sequence whose partial sums are the Chebyshev error. -/
def mertensCoeff (i : ℕ) : ℂ := (vonMangoldt (i + 1) : ℂ) - 1

theorem coeffPartial_mertensCoeff (n : ℕ) :
    coeffPartial mertensCoeff n = ((Chebyshev.psi (n : ℝ) : ℝ) : ℂ) - (n : ℂ) := by
  rw [coeffPartial, psi_natCast_eq_sum_range]
  simp only [mertensCoeff]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem coeffPartial_mertensCoeff_succ (k : ℕ) :
    coeffPartial mertensCoeff (k + 1) = ((psiError k : ℝ) : ℂ) := by
  rw [coeffPartial_mertensCoeff, psiError]
  push_cast
  ring

/-- The shifted Dirichlet weight is the `L`-series term. -/
theorem cpow_neg_mul_eq_term (f : ℕ → ℂ) (s : ℂ) (i : ℕ) :
    ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) * f (i + 1) = LSeries.term f s (i + 1) := by
  rw [LSeries.term_def, if_neg (Nat.succ_ne_zero i), Complex.cpow_neg, div_eq_mul_inv]
  push_cast
  ring

theorem summable_vonMangoldtShift {s : ℝ} (hs : 1 < s) :
    Summable fun i : ℕ =>
      ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * (vonMangoldt (i + 1) : ℂ) := by
  have hre : 1 < ((s : ℂ)).re := by simpa using hs
  have h := (summable_nat_add_iff (f := LSeries.term (fun n => (vonMangoldt n : ℂ)) (s : ℂ)) 1).2
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hre)
  exact h.congr fun i => (cpow_neg_mul_eq_term (fun n => (vonMangoldt n : ℂ)) (s : ℂ) i).symm

theorem summable_oneShift {s : ℝ} (hs : 1 < s) :
    Summable fun i : ℕ => ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * (1 : ℂ) := by
  have hre : 1 < ((s : ℂ)).re := by simpa using hs
  have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ (s : ℂ)) 1).2
    (Complex.summable_one_div_nat_cpow.2 hre)
  refine h.congr fun i => ?_
  rw [mul_one, Complex.cpow_neg, one_div]
  push_cast
  ring

theorem summable_mertensDirichlet {s : ℝ} (hs : 1 < s) :
    Summable fun i : ℕ => ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * mertensCoeff i := by
  have hsplit : ∀ i : ℕ, ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * mertensCoeff i
      = ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * (vonMangoldt (i + 1) : ℂ)
        - ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * (1 : ℂ) := by
    intro i
    rw [mertensCoeff]
    ring
  exact ((summable_vonMangoldtShift hs).sub (summable_oneShift hs)).congr fun i => (hsplit i).symm

/-- **The Dirichlet series of `Λ − 1` is `L(Λ, s) − ζ(s)`.** -/
theorem tsum_mertensDirichlet {s : ℝ} (hs : 1 < s) :
    (∑' i : ℕ, ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * mertensCoeff i)
      = LSeries (fun n => (vonMangoldt n : ℂ)) (s : ℂ) - riemannZeta (s : ℂ) := by
  have hre : 1 < ((s : ℂ)).re := by simpa using hs
  have hsplit : ∀ i : ℕ, ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * mertensCoeff i
      = ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * (vonMangoldt (i + 1) : ℂ)
        - ((((i : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) * (1 : ℂ) := by
    intro i
    rw [mertensCoeff]
    ring
  rw [tsum_congr hsplit, (summable_vonMangoldtShift hs).tsum_sub (summable_oneShift hs)]
  congr 1
  · simp only [LSeries]
    rw [(ArithmeticFunction.LSeriesSummable_vonMangoldt hre).tsum_eq_zero_add, LSeries.term_zero,
      zero_add]
    exact tsum_congr fun i => cpow_neg_mul_eq_term (fun n => (vonMangoldt n : ℂ)) (s : ℂ) i
  · rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
    refine tsum_congr fun i => ?_
    rw [mul_one, Complex.cpow_neg, one_div]
    push_cast
    ring

/-- The Chebyshev error is eventually at most the argument. -/
theorem eventually_abs_psi_sub_le : ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ x := by
  filter_upwards [tendsto_psi_div_self.eventually_lt_const (by norm_num : (1 : ℝ) < 2),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hpsi : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
  rw [div_lt_iff₀ hx0] at hx
  rw [abs_le]
  constructor <;> linarith

theorem tendsto_boundary_mertens {s : ℝ} (hs : 1 < s) :
    Tendsto (fun n : ℕ => ((n : ℝ) : ℂ) ^ (-(s : ℂ)) * coeffPartial mertensCoeff n) atTop
      (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => ((n : ℝ)) ^ (-(s - 1))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < s - 1)).comp tendsto_natCast_atTop_atTop
  refine squeeze_zero_norm' ?_ hlim
  obtain ⟨X, hX⟩ := eventually_atTop.1 ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    eventually_abs_psi_sub_le)
  filter_upwards [eventually_atTop.2 ⟨X, hX⟩, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hnpos, coeffPartial_mertensCoeff]
  have hnorm : ‖((Chebyshev.psi (n : ℝ) : ℝ) : ℂ) - (n : ℂ)‖ = |Chebyshev.psi (n : ℝ) - (n : ℝ)| := by
    rw [show ((Chebyshev.psi (n : ℝ) : ℝ) : ℂ) - (n : ℂ)
        = (((Chebyshev.psi (n : ℝ) - (n : ℝ)) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  have hre : ((-(s : ℂ))).re = -s := by simp
  rw [hre]
  have hstep : (n : ℝ) ^ (-s) * |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤ (n : ℝ) ^ (-s) * (n : ℝ) :=
    mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hnpos.le _)
  refine hstep.trans (le_of_eq ?_)
  rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]

/-- The Abel tail of the Dirichlet difference. -/
def mertensDirichletTail (s : ℝ) : ℂ :=
  ∑' k : ℕ, ((psiError k : ℝ) : ℂ)
    * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-(s : ℂ)))

theorem mertensDirichletTail_eq (s : ℝ) :
    mertensDirichletTail s = ∑' k : ℕ, ((psiError k : ℝ) : ℂ)
      * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-(s : ℂ))) := rfl

theorem summable_mertensAbelTerm {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) :
    Summable fun k : ℕ => coeffPartial mertensCoeff (k + 1)
      * (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-(s : ℂ)) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-(s : ℂ))) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    summable_absPsiError_weight)
  rw [coeffPartial_mertensCoeff_succ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_cpow_increment_le k hs1 hs2) (abs_nonneg _)

/-- **The Dirichlet difference is the Abel tail of the Chebyshev error.** -/
theorem mertensDirichlet_eq_tail {s : ℝ} (hs1 : 1 < s) (hs2 : s < 2) :
    LSeries (fun n => (vonMangoldt n : ℂ)) (s : ℂ) - riemannZeta (s : ℂ)
      = mertensDirichletTail s := by
  rw [← tsum_mertensDirichlet hs1,
    tsum_eq_abelTail (summable_mertensDirichlet hs1) (summable_mertensAbelTerm hs1.le hs2.le)
      (tendsto_boundary_mertens hs1), mertensDirichletTail_eq]
  exact tsum_congr fun k => by rw [coeffPartial_mertensCoeff_succ]

theorem tendsto_mertensDirichletTail :
    Tendsto mertensDirichletTail (𝓝[>] 1) (𝓝 ((mertensAbelTail : ℝ) : ℂ)) := by
  have h := tendsto_tsum_cpow_increment (E := fun k : ℕ => ((psiError k : ℝ) : ℂ))
    summable_absPsiError_weight
    (fun k => le_of_eq (by rw [Complex.norm_real, Real.norm_eq_abs]))
  have hval : (∑' k : ℕ, ((psiError k : ℝ) : ℂ)
      * (((((k : ℝ) + 1 : ℝ)) : ℂ)⁻¹ - ((((k : ℝ) + 2 : ℝ)) : ℂ)⁻¹))
      = ((mertensAbelTail : ℝ) : ℂ) := by
    rw [mertensAbelTail, Complex.ofReal_tsum]
    exact tsum_congr fun k => by push_cast; ring
  rw [hval] at h
  exact h.congr fun s => (mertensDirichletTail_eq s).symm

/-- **The Abel tail constant of the Chebyshev error is `−2γ`.** -/
theorem mertensAbelTail_eq : mertensAbelTail = -2 * Real.eulerMascheroniConstant := by
  have hid : ∀ᶠ s : ℝ in 𝓝[>] 1,
      LSeries (fun n => (vonMangoldt n : ℂ)) (s : ℂ) - riemannZeta (s : ℂ)
        = mertensDirichletTail s := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))] with s hs hs2
    exact mertensDirichlet_eq_tail hs hs2
  have h := mertensTail_eq hid tendsto_mertensDirichletTail
  have hcast : ((mertensAbelTail : ℝ) : ℂ) = ((-2 * Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast hcast

/-! ## Mertens' second theorem -/

/-- **Mertens' second theorem.**  `∑_{n ≤ N} Λ(n)/n − log N → −γ`. -/
theorem tendsto_sum_vonMangoldt_div_sub_log :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / (n : ℝ))
        - Real.log (N : ℝ)) atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hbase : Tendsto (fun n : ℕ =>
      (∑ i ∈ Finset.range (n + 1), (vonMangoldt (i + 1) : ℝ) / ((i : ℝ) + 1))
        - Real.log ((n : ℝ) + 1)) atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h := tendsto_vonMangoldt_harmonicWeighted
    rw [mertensAbelTail_eq,
      show Real.eulerMascheroniConstant + -2 * Real.eulerMascheroniConstant
        = -Real.eulerMascheroniConstant by ring] at h
    exact h
  refine (hbase.comp (tendsto_sub_atTop_nat 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hstep : N - 1 + 1 = N := by omega
  have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    rw [show ((N - 1 : ℕ) : ℝ) + 1 = (((N - 1 : ℕ) + 1 : ℕ) : ℝ) by push_cast; ring, hstep]
  simp only [Function.comp_apply]
  rw [hstep, hcast]
  congr 1
  rw [sum_Icc_eq_sum_range_shift (fun n => (vonMangoldt n : ℝ) / (n : ℝ)) N]
  exact Finset.sum_congr rfl fun i _ => by push_cast; ring

/-! ## The limit of the harmonic primitive -/

theorem harmonic_eq_sum_Icc (N : ℕ) : (harmonic N : ℝ) = ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) := by
  rw [sum_Icc_eq_sum_range_shift (fun n => 1 / (n : ℝ)) N, harmonic]
  push_cast
  exact Finset.sum_congr rfl fun i _ => by rw [one_div]

theorem sourcePartialSum_vonMangoldt_sub_one (N : ℕ) :
    sourcePartialSum (fun n => (vonMangoldt n : ℝ) - 1) N = Chebyshev.psi (N : ℝ) - (N : ℝ) := by
  rw [sourcePartialSum, Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul,
    mul_one, sum_Icc_eq_sum_range_shift (fun n => (vonMangoldt n : ℝ)) N,
    psi_natCast_eq_sum_range, Nat.add_sub_cancel]

theorem tendsto_psiError_div :
    Tendsto (fun N : ℕ => (Chebyshev.psi (N : ℝ) - (N : ℝ)) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hz : Tendsto (fun N : ℕ => |Chebyshev.psi (N : ℝ) / (N : ℝ) - 1|) atTop (𝓝 0) := by
    have h := tendsto_psi_natCast_div.sub_const 1
    rw [sub_self] at h
    simpa [Real.norm_eq_abs] using tendsto_zero_iff_norm_tendsto_zero.1 h
  refine squeeze_zero_norm' ?_ hz
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hq : |Chebyshev.psi (N : ℝ) / (N : ℝ) - 1|
      = |Chebyshev.psi (N : ℝ) - (N : ℝ)| / (N : ℝ) := by
    rw [show Chebyshev.psi (N : ℝ) / (N : ℝ) - 1
        = (Chebyshev.psi (N : ℝ) - (N : ℝ)) / (N : ℝ) by field_simp]
    rw [abs_div, abs_of_pos hNpos]
  rw [hq, Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : (0 : ℝ) < (N : ℝ) + 1)]
  gcongr
  linarith

/-- **(24.64) The harmonic primitive of the Chebyshev error tends to `−2γ`.** -/
theorem tendsto_harmonicPrimitive_vonMangoldt :
    Tendsto (fun N : ℕ =>
        harmonicPrimitive (sourcePartialSum (fun n => (vonMangoldt n : ℝ) - 1)) N)
      atTop (𝓝 (-2 * Real.eulerMascheroniConstant)) := by
  have hmain := tendsto_harmonicPrimitive_of_mertens
    (S := fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / (n : ℝ))
    (R := fun N : ℕ => Chebyshev.psi (N : ℝ) - (N : ℝ))
    tendsto_psiError_div tendsto_sum_vonMangoldt_div_sub_log
  refine hmain.congr fun N => ?_
  rw [harmonicPrimitive_sourcePartialSum, sourcePartialSum_vonMangoldt_sub_one,
    harmonic_eq_sum_Icc]
  have hsplit : ∑ n ∈ Finset.Icc 1 N, ((vonMangoldt n : ℝ) - 1) / (n : ℝ)
      = (∑ n ∈ Finset.Icc 1 N, (vonMangoldt n : ℝ) / (n : ℝ))
        - ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hsplit]

end

end RHTower
