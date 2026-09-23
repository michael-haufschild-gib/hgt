/-
# The Laurent tail of `t ↦ t ^ L * g t⁻¹` and the gap dichotomy

Let `g` be analytic at `0` and `L : ℕ`.  Taylor's theorem splits `g` into its degree-`L` part plus a
remainder `x ^ (L+1) * F x`, so

  `t ^ L * g t⁻¹ = Poly.eval t + t⁻¹ * F t⁻¹`,  `Poly.natDegree ≤ L`.

Differentiating `L + 1` times kills `Poly`, and the recursion `A_{j+1} x = -x^(2 : ℕ) * A_j' x`
(`tailSeq`) transports `d/dt` through `t ↦ t⁻¹`, so the `(L+1)`-st derivative of the left-hand side
is `A_{L+1} t⁻¹`, whose analytic order at `0` is `k + L + 3` where `k` is the order of `F`.  This
gives a two-sided control of the top derivative, which the divided-difference estimate converts into
the gap property `Thin`.

The dichotomy `thin_or_eventually_poly` is exactly the case split (a)/(c) of Coleman--Zwald: either
`t ^ L * g t⁻¹` is eventually a polynomial in `t`, or the set of integers where it takes integer
values is gap thin.
-/
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.ThinSets
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.DividedDifference

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Filter Topology Polynomial

/-! ### The derivative recursion through `t ↦ t⁻¹` -/

/-- The recursion `A_{j+1}(x) = -x^(2 : ℕ) * A_j'(x)`, which transports `d/dt` through `t ↦ t⁻¹`. -/
noncomputable def tailSeq (F : ℝ → ℝ) : ℕ → (ℝ → ℝ)
  | 0 => fun x => x * F x
  | (j + 1) => fun x => -(x ^ (2 : ℕ) * deriv (tailSeq F j) x)

theorem tailSeq_zero (F : ℝ → ℝ) : tailSeq F 0 = fun x => x * F x := rfl

theorem tailSeq_succ (F : ℝ → ℝ) (j : ℕ) :
    tailSeq F (j + 1) = fun x => -(x ^ (2 : ℕ) * deriv (tailSeq F j) x) := rfl

theorem analyticAt_tailSeq {F : ℝ → ℝ} (hF : AnalyticAt ℝ F 0) (j : ℕ) :
    AnalyticAt ℝ (tailSeq F j) 0 := by
  induction j with
  | zero => exact (analyticAt_id).mul hF
  | succ j ih =>
      rw [tailSeq_succ]
      exact (((analyticAt_id).pow 2).mul ih.deriv).neg

theorem analyticOrderAt_sq : analyticOrderAt (fun x : ℝ => x ^ (2 : ℕ)) 0 = ((2 : ℕ) : ℕ∞) := by
  have hfun : (fun x : ℝ => x ^ (2 : ℕ)) = (id : ℝ → ℝ) ^ (2 : ℕ) := by funext x; simp
  rw [hfun, analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
  simp

/-- **Each derivative raises the vanishing order by one.** -/
theorem analyticOrderAt_tailSeq {F : ℝ → ℝ} (hF : AnalyticAt ℝ F 0) {k : ℕ}
    (hFk : analyticOrderAt F 0 = (k : ℕ∞)) (j : ℕ) :
    analyticOrderAt (tailSeq F j) 0 = ((k + j + 1 : ℕ) : ℕ∞) := by
  induction j with
  | zero =>
      rw [tailSeq_zero]
      have hid : (fun x : ℝ => x * F x) = id * F := by funext x; rfl
      rw [hid, analyticOrderAt_mul analyticAt_id hF, analyticOrderAt_id, hFk]
      push_cast
      ring
  | succ j ih =>
      have hder : analyticOrderAt (deriv (tailSeq F j)) 0 = ((k + j : ℕ) : ℕ∞) := by
        refine analyticOrderAt_deriv_of_pos (analyticAt_tailSeq hF j) (n := k + j) ?_
        rw [ih]; push_cast; ring
      rw [tailSeq_succ]
      have hneg : analyticOrderAt (fun x : ℝ => -(x ^ (2 : ℕ) * deriv (tailSeq F j) x)) 0
          = analyticOrderAt (fun x : ℝ => x ^ (2 : ℕ) * deriv (tailSeq F j) x) 0 := by
        have h : (fun x : ℝ => -(x ^ (2 : ℕ) * deriv (tailSeq F j) x))
            = -(fun x : ℝ => x ^ (2 : ℕ) * deriv (tailSeq F j) x) := by funext x; rfl
        rw [h, analyticOrderAt_neg]
      rw [hneg]
      have hmul : (fun x : ℝ => x ^ (2 : ℕ) * deriv (tailSeq F j) x)
          = (fun x : ℝ => x ^ (2 : ℕ)) * deriv (tailSeq F j) := by funext x; rfl
      rw [hmul, analyticOrderAt_mul (by fun_prop) (analyticAt_tailSeq hF j).deriv,
        analyticOrderAt_sq, hder]
      push_cast
      ring

/-- Transport of the derivative through `t ↦ t⁻¹`: this is what the recursion encodes. -/
theorem hasDerivAt_tailSeq_inv {F : ℝ → ℝ} {j : ℕ} {t : ℝ} (ht : t ≠ 0)
    (hA : AnalyticAt ℝ (tailSeq F j) t⁻¹) :
    HasDerivAt (fun s : ℝ => tailSeq F j s⁻¹) (tailSeq F (j + 1) t⁻¹) t := by
  have hinv : HasDerivAt (fun s : ℝ => s⁻¹) (-(t ^ (2 : ℕ))⁻¹) t := hasDerivAt_inv ht
  have houter : HasDerivAt (tailSeq F j) (deriv (tailSeq F j) t⁻¹) t⁻¹ :=
    hA.differentiableAt.hasDerivAt
  have hcomp := houter.comp t hinv
  have hval : deriv (tailSeq F j) t⁻¹ * -(t ^ (2 : ℕ))⁻¹ = tailSeq F (j + 1) t⁻¹ := by
    show _ = -((t⁻¹) ^ (2 : ℕ) * deriv (tailSeq F j) t⁻¹)
    rw [inv_pow]
    ring
  simpa [Function.comp_def, hval] using hcomp

/-- The full derivative sequence of `t ↦ t ^ L * g t⁻¹`: polynomial part plus tail. -/
noncomputable def bigD (Poly : ℝ[X]) (F : ℝ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ((Polynomial.derivative)^[j] Poly).eval t + tailSeq F j t⁻¹

theorem hasDerivAt_bigD {Poly : ℝ[X]} {F : ℝ → ℝ} {j : ℕ} {t : ℝ} (ht : t ≠ 0)
    (hA : AnalyticAt ℝ (tailSeq F j) t⁻¹) :
    HasDerivAt (bigD Poly F j) (bigD Poly F (j + 1) t) t := by
  have h1 : HasDerivAt (fun s => ((Polynomial.derivative)^[j] Poly).eval s)
      (((Polynomial.derivative)^[j + 1] Poly).eval t) t := by
    rw [Function.iterate_succ_apply']
    exact Polynomial.hasDerivAt _ t
  exact h1.add (hasDerivAt_tailSeq_inv ht hA)

/-! ### The Taylor split -/

/-- The reversed degree-`L` Taylor polynomial of `g` at `0`. -/
noncomputable def tailPoly (g : ℝ → ℝ) (L : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (L + 1),
    Polynomial.C (iteratedDeriv i g 0 / (i.factorial : ℝ)) * Polynomial.X ^ (L - i)

theorem natDegree_tailPoly_le (g : ℝ → ℝ) (L : ℕ) : (tailPoly g L).natDegree ≤ L := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine le_trans (Polynomial.natDegree_mul_le) ?_
  simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add]
  omega

/-- **Taylor split.**  `t ^ L * g t⁻¹` is a polynomial of degree `≤ L` plus `t⁻¹ * F t⁻¹`. -/
theorem exists_tail_split {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) (L : ℕ) :
    ∃ F : ℝ → ℝ, AnalyticAt ℝ F 0 ∧
      ∀ t : ℝ, t ≠ 0 → t ^ L * g t⁻¹ = (tailPoly g L).eval t + t⁻¹ * F t⁻¹ := by
  obtain ⟨F, hFa, hFeq⟩ := hg.exists_eq_sum_add_pow_mul (L + 1)
  refine ⟨F, hFa, fun t ht => ?_⟩
  rw [hFeq t⁻¹]
  have hterm : ∀ i ∈ Finset.range (L + 1),
      t ^ L * ((t⁻¹ ^ i / (i.factorial : ℝ)) • iteratedDeriv i g 0)
        = (iteratedDeriv i g 0 / (i.factorial : ℝ)) * t ^ (L - i) := by
    intro i hi
    have hiL : i ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsplit : t ^ L = t ^ (L - i) * t ^ i := by
      rw [← pow_add]
      congr 1
      omega
    have hpow : t ^ L * t⁻¹ ^ i = t ^ (L - i) := by
      rw [hsplit, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero i ht), mul_one]
    simp only [smul_eq_mul]
    have hrw : t ^ L * (t⁻¹ ^ i / (i.factorial : ℝ) * iteratedDeriv i g 0)
        = (t ^ L * t⁻¹ ^ i) * (iteratedDeriv i g 0 / (i.factorial : ℝ)) := by ring
    rw [hrw, hpow]
    ring
  have hlast : t ^ L * (t⁻¹ ^ (L + 1) • F t⁻¹) = t⁻¹ * F t⁻¹ := by
    have hpl : t ^ L * t⁻¹ ^ (L + 1) = t⁻¹ := by
      rw [inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero L ht), one_mul]
    simp only [smul_eq_mul]
    rw [← mul_assoc, hpl]
  rw [mul_add, Finset.mul_sum, hlast, Finset.sum_congr rfl hterm]
  congr 1
  rw [tailPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun i _ => by simp

/-! ### The dichotomy -/

/-- **Case split (a)/(c) of Coleman--Zwald.**  Either `t ↦ t ^ L * g t⁻¹` is eventually a polynomial
of degree `≤ L`, or the set of integers at which it takes integer values is gap thin. -/
theorem thin_or_eventually_poly (L : ℕ) {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0) (S : Set ℤ)
    (hS : ∀ n ∈ S, ∃ N : ℤ, (n : ℝ) ^ L * g ((n : ℝ))⁻¹ = (N : ℝ)) :
    Thin S ∨ ∃ p : ℝ[X], p.natDegree ≤ L ∧ ∃ T : ℝ, ∀ t : ℝ, T < t → t ^ L * g t⁻¹ = p.eval t := by
  classical
  obtain ⟨F, hFa, hFeq⟩ := exists_tail_split hg L
  set Poly : ℝ[X] := tailPoly g L with hPolyDef
  have hPolyDeg : Poly.natDegree ≤ L := natDegree_tailPoly_le g L
  by_cases hFtop : analyticOrderAt F 0 = ⊤
  · -- (a) the tail vanishes identically: the function is a polynomial far out
    right
    refine ⟨Poly, hPolyDeg, ?_⟩
    rw [analyticOrderAt_eq_top] at hFtop
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hFtop
    refine ⟨max ρ⁻¹ 1, fun t ht => ?_⟩
    have ht1 : (1 : ℝ) < t := lt_of_le_of_lt (le_max_right _ _) ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    have htρ : t⁻¹ < ρ := by
      have hρi : ρ⁻¹ < t := lt_of_le_of_lt (le_max_left _ _) ht
      exact inv_lt_of_inv_lt₀ hρ hρi
    have hFz : F t⁻¹ = 0 := by
      refine hball ?_
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
      exact htρ
    rw [hFeq t (ne_of_gt ht0), hFz, mul_zero, add_zero]
  · -- (c) the tail has finite order: the gap estimate applies
    left
    set k : ℕ := (analyticOrderAt F 0).toNat with hkDef
    have hFk : analyticOrderAt F 0 = (k : ℕ∞) := (ENat.coe_toNat hFtop).symm
    set m : ℕ := L + 1 with hmDef
    have hm : 0 < m := Nat.succ_pos L
    set q : ℕ := k + m + 1 with hqDef
    have hOrd : analyticOrderAt (tailSeq F m) 0 = (q : ℕ∞) :=
      analyticOrderAt_tailSeq hFa hFk m
    obtain ⟨h, hha, hh0, hheq⟩ :=
      (AnalyticAt.analyticOrderAt_eq_natCast (analyticAt_tailSeq hFa m)).1 hOrd
    have hh0pos : 0 < |h 0| := abs_pos.mpr hh0
    -- a single ball on which everything is available
    have hev : ∀ᶠ x in 𝓝 (0 : ℝ),
        (∀ j ∈ Finset.range (m + 1), AnalyticAt ℝ (tailSeq F j) x) ∧
        tailSeq F m x = (x - 0) ^ q • h x ∧ |h x - h 0| < |h 0| / 2 := by
      refine Filter.Eventually.and ?_ (Filter.Eventually.and hheq ?_)
      · exact Filter.eventually_all_finset _ |>.mpr
          fun j _ => (analyticAt_tailSeq hFa j).eventually_analyticAt
      · have htend : Filter.Tendsto h (𝓝 (0 : ℝ)) (𝓝 (h 0)) := hha.continuousAt.tendsto
        have := htend (Metric.ball_mem_nhds (h 0) (by positivity : (0:ℝ) < |h 0| / 2))
        filter_upwards [this] with x hx
        simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hx
        exact hx
    obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    set T : ℝ := max ρ⁻¹ 1 with hTDef
    have hballspec : ∀ x : ℝ, 0 < x → x < ρ →
        (∀ j ∈ Finset.range (m + 1), AnalyticAt ℝ (tailSeq F j) x) ∧
        tailSeq F m x = (x - 0) ^ q • h x ∧ |h x - h 0| < |h 0| / 2 := by
      intro x hx0 hxρ
      refine hball ?_
      rw [Real.dist_eq, sub_zero, abs_of_pos hx0]
      exact hxρ
    have hTinv : ∀ t : ℝ, T < t → 0 < t ∧ t⁻¹ < ρ ∧ 0 < t⁻¹ := by
      intro t ht
      have ht1 : (1 : ℝ) < t := lt_of_le_of_lt (le_max_right _ _) ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
      refine ⟨ht0, ?_, by positivity⟩
      have hρi : ρ⁻¹ < t := lt_of_le_of_lt (le_max_left _ _) ht
      exact inv_lt_of_inv_lt₀ hρ hρi
    -- the top derivative of `Poly` vanishes
    have hPolyTop : (Polynomial.derivative)^[m] Poly = 0 := by
      have hle : Poly.natDegree ≤ m := le_trans hPolyDeg (Nat.le_succ L)
      rw [iterate_derivative_eq_C hle,
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hPolyDeg (Nat.lt_succ_self L))]
      simp
    refine ⟨m, q, m * (m + 1), T, (m.factorial : ℝ) / (4 * |h 0|), by positivity,
      by omega, by positivity, ?_⟩
    intro τ hτmono hτT hτS
    set t : Fin (m + 1) → ℝ := fun i => ((τ i : ℤ) : ℝ) with htDef
    have htmono : StrictMono t := fun i j hij => by
      simpa [htDef] using (Int.cast_lt (R := ℝ)).2 (hτmono hij)
    have htT : ∀ i, T < t i := hτT
    have ht0 : ∀ i, 0 < t i := fun i => (hTinv _ (htT i)).1
    have ht00 : (0 : ℝ) < t 0 := ht0 0
    have htq : (0 : ℝ) < (t 0) ^ q := pow_pos ht00 q
    have htqi : (0 : ℝ) < ((t 0)⁻¹) ^ q := pow_pos (inv_pos.mpr ht00) q
    have hDderiv : ∀ j, j < m → ∀ x ∈ Set.Ioi T,
        HasDerivAt (bigD Poly F j) (bigD Poly F (j + 1) x) x := by
      intro j hj x hx
      have hx' := hTinv x hx
      exact hasDerivAt_bigD (ne_of_gt hx'.1)
        ((hballspec x⁻¹ hx'.2.2 hx'.2.1).1 j (Finset.mem_range.mpr (by omega)))
    have hsubIcc : Set.Icc (t 0) (t (Fin.last m)) ⊆ Set.Ioi T := fun x hx =>
      lt_of_lt_of_le (htT 0) hx.1
    obtain ⟨u, hu, hval⟩ := exists_dividedDiff_eq hm (bigD Poly F) hDderiv t htmono hsubIcc
    have huT : T < u := lt_trans (htT 0) hu.1
    have hupos : 0 < u := (hTinv u huT).1
    have huinv := hTinv u huT
    have hspec := hballspec u⁻¹ huinv.2.2 huinv.2.1
    have hDm : bigD Poly F m u = (u⁻¹) ^ q * h (u⁻¹) := by
      rw [bigD, hPolyTop]
      simpa using hspec.2.1
    have hhne : h (u⁻¹) ≠ 0 := by
      intro hz
      have hlt := hspec.2.2
      rw [hz, zero_sub, abs_neg] at hlt
      linarith
    have hhbound : |h (u⁻¹)| ≤ 2 * |h 0| := by
      have hlt := hspec.2.2
      have habs := abs_sub_abs_le_abs_sub (h u⁻¹) (h 0)
      linarith
    have hfact : (0 : ℝ) < (m.factorial : ℝ) := by positivity
    have hDmne : bigD Poly F m u ≠ 0 := by
      rw [hDm]
      exact mul_ne_zero (pow_ne_zero q (ne_of_gt huinv.2.2)) hhne
    have hddne : dividedDiff (bigD Poly F 0) t ≠ 0 := by
      rw [hval]
      exact div_ne_zero hDmne (ne_of_gt hfact)
    have hinj : Function.Injective t := htmono.injective
    have hvals : ∀ i, ∃ N : ℤ, bigD Poly F 0 (t i) = (N : ℝ) := by
      intro i
      obtain ⟨N, hN⟩ := hS (τ i) (hτS i)
      refine ⟨N, ?_⟩
      rw [bigD]
      simp only [Function.iterate_zero, id_eq, tailSeq_zero]
      rw [← hFeq (t i) (ne_of_gt (ht0 i))]
      exact hN
    choose N hN using hvals
    have hprod := dividedDiff_mul_nodeProd (bigD Poly F 0) hinj
    set Z : ℤ := ∑ i, N i * ∏ k ∈ Finset.univ.erase i, ∏ j ∈ Finset.univ.erase k, (τ k - τ j)
      with hZDef
    have hZ : dividedDiff (bigD Poly F 0) t * nodeProd t = (Z : ℝ) := by
      rw [hprod, hZDef]
      push_cast
      exact Finset.sum_congr rfl fun i _ => by rw [hN i]
    have hnpne : nodeProd t ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => prod_erase_ne_zero hinj i
    have hZne : Z ≠ 0 := by
      intro hz
      rw [hz] at hZ
      exact (mul_ne_zero hddne hnpne) (by simpa using hZ)
    have hZ1 : (1 : ℝ) ≤ |dividedDiff (bigD Poly F 0) t * nodeProd t| := by
      rw [hZ, ← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hZne
    -- spread bound on the node product
    have hBpos : 0 < t (Fin.last m) - t 0 := by
      have := htmono (show (0 : Fin (m + 1)) < Fin.last m by
        simpa [Fin.lt_def] using hm)
      linarith
    have hspread : ∀ i j : Fin (m + 1), |t i - t j| ≤ t (Fin.last m) - t 0 := by
      intro i j
      have hi1 : t 0 ≤ t i := htmono.monotone (Fin.zero_le _)
      have hi2 : t i ≤ t (Fin.last m) := htmono.monotone (Fin.le_last _)
      have hj1 : t 0 ≤ t j := htmono.monotone (Fin.zero_le _)
      have hj2 : t j ≤ t (Fin.last m) := htmono.monotone (Fin.le_last _)
      rw [abs_le]
      constructor <;> linarith
    have hnp : |nodeProd t| ≤ (t (Fin.last m) - t 0) ^ (m * (m + 1)) := by
      rw [nodeProd, Finset.abs_prod]
      have hstep : ∀ i : Fin (m + 1),
          |∏ j ∈ Finset.univ.erase i, (t i - t j)| ≤ (t (Fin.last m) - t 0) ^ m := by
        intro i
        rw [Finset.abs_prod]
        have hcard : (Finset.univ.erase i).card = m := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp
        calc ∏ j ∈ Finset.univ.erase i, |t i - t j|
            ≤ ∏ _j ∈ Finset.univ.erase i, (t (Fin.last m) - t 0) :=
              Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hspread i j)
          _ = (t (Fin.last m) - t 0) ^ m := by rw [Finset.prod_const, hcard]
      calc ∏ i, |∏ j ∈ Finset.univ.erase i, (t i - t j)|
          ≤ ∏ _i : Fin (m + 1), (t (Fin.last m) - t 0) ^ m :=
            Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hstep i)
        _ = (t (Fin.last m) - t 0) ^ (m * (m + 1)) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
    -- upper bound on the divided difference
    have hutinv : u⁻¹ ≤ (t 0)⁻¹ := by
      exact inv_anti₀ ht00 (le_of_lt hu.1)
    have h5 : (m.factorial : ℝ) * |dividedDiff (bigD Poly F 0) t| * (t 0) ^ q ≤ 2 * |h 0| := by
      have habs : (m.factorial : ℝ) * |dividedDiff (bigD Poly F 0) t| = |bigD Poly F m u| := by
        rw [hval, abs_div, abs_of_pos hfact]
        field_simp
      rw [habs, hDm, abs_mul, abs_pow, abs_of_pos huinv.2.2]
      have hstep1 : (u⁻¹) ^ q * |h u⁻¹| ≤ ((t 0)⁻¹) ^ q * (2 * |h 0|) := by
        refine mul_le_mul (pow_le_pow_left₀ (le_of_lt huinv.2.2) hutinv q) hhbound
          (abs_nonneg _) (le_of_lt htqi)
      calc (u⁻¹) ^ q * |h u⁻¹| * (t 0) ^ q
          ≤ ((t 0)⁻¹) ^ q * (2 * |h 0|) * (t 0) ^ q :=
            mul_le_mul_of_nonneg_right hstep1 (le_of_lt htq)
        _ = 2 * |h 0| := by
            rw [inv_pow]
            field_simp
    -- combine
    have h4 : (1 : ℝ) ≤ |dividedDiff (bigD Poly F 0) t| * (t (Fin.last m) - t 0) ^ (m * (m + 1)) := by
      rw [abs_mul] at hZ1
      exact le_trans hZ1 (mul_le_mul_of_nonneg_left hnp (abs_nonneg _))
    have hkey : (m.factorial : ℝ) * (t 0) ^ q
        ≤ 2 * |h 0| * (t (Fin.last m) - t 0) ^ (m * (m + 1)) := by
      have hBE : (0 : ℝ) < (t (Fin.last m) - t 0) ^ (m * (m + 1)) := pow_pos hBpos _
      have hstep : (m.factorial : ℝ) * (t 0) ^ q
          ≤ (m.factorial : ℝ) * (t 0) ^ q *
            (|dividedDiff (bigD Poly F 0) t| * (t (Fin.last m) - t 0) ^ (m * (m + 1))) :=
        le_mul_of_one_le_right (le_of_lt (mul_pos hfact htq)) h4
      have hrw : (m.factorial : ℝ) * (t 0) ^ q *
          (|dividedDiff (bigD Poly F 0) t| * (t (Fin.last m) - t 0) ^ (m * (m + 1)))
          = ((m.factorial : ℝ) * |dividedDiff (bigD Poly F 0) t| * (t 0) ^ q) *
            (t (Fin.last m) - t 0) ^ (m * (m + 1)) := by ring
      rw [hrw] at hstep
      exact le_trans hstep (mul_le_mul_of_nonneg_right h5 (le_of_lt hBE))
    have hBE : (0 : ℝ) < (t (Fin.last m) - t 0) ^ (m * (m + 1)) := pow_pos hBpos _
    have hgoal : (m.factorial : ℝ) / (4 * |h 0|) * (t 0) ^ q
        = ((m.factorial : ℝ) * (t 0) ^ q) / (4 * |h 0|) := by ring
    rw [hgoal, div_lt_iff₀ (by positivity)]
    nlinarith [hkey, hBE, hh0pos]

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
