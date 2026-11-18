import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.ConductorGraphJetSections
import GaloisForLFunctions.BiarithmeticGaugeGeometry.EuclideanCellRemainderAndPolarNeutralCollapse
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Subquadratic height of simultaneous jet interpolation

On a fixed conductor window starting at N = ⌊√m⌋ the graph ordinates have
unit-disk norm at most the square of the largest conductor. Both sampled
multiplicities have size O(m/√N). Clearing every Hermite interpolation
denominator and lifting bounded data therefore costs o(m²) in log norm,
uniformly over the closed unit bidisk.
-/

noncomputable section
open Polynomial Finset Filter Topology
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem graph_disk_bound (e : ℤ[X] →+* ℂ) (he : ‖e X‖ ≤ 1) (n : ℕ) :
    ‖e (conductorGraph n)‖ ≤ (n : ℝ)^2 := by
  rw [conductorGraph, map_sum]
  apply (norm_sum_le _ _).trans
  have ht (d : ℕ) (hd : d ∈ n.divisors) :
      ‖e (monomial d ((∏ p ∈ d.primeFactors, p : ℕ) : ℤ))‖ ≤ (n : ℝ) := by
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
    apply (mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ (norm_nonneg _) he)).trans
    exact_mod_cast (Nat.le_of_dvd (Nat.pos_of_mem_divisors hd) (Nat.prod_primeFactors_dvd d)).trans
      (Nat.divisor_le hd)
  have hs := sum_le_sum ht
  simp only [sum_const, nsmul_eq_mul] at hs
  rw [sq]
  exact hs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self n)
    (Nat.cast_nonneg n))

/-- Maximum uniform jet order for ceiling-rounded weights of size C m / √N. -/
def meshJetOrder (C : ℕ) (m : ℕ) : ℕ := ⌈(C : ℝ)*m / Real.sqrt m.sqrt⌉₊ + 1

/-- The order covers both integer thickenings used for the lower and upper
graph on the logarithmic mesh, with arbitrary signs of the two samples. -/
theorem sampledGraph_jetOrders_le (C m i : ℕ) (hm : 0 < m) (hi : m.sqrt ≤ i)
    (x y : ℝ) (hx : |x| ≤ C) (hy : |y| ≤ C) :
    ⌊(m:ℝ)*(Real.sqrt i * BiarithmeticGaugeGeometry.logCellWidth i * x)⌋.natAbs ≤ meshJetOrder C m ∧
    ⌊(m:ℝ)*(y / Real.sqrt i)⌋.natAbs ≤ meshJetOrder C m := by
  have hN : 0 < m.sqrt := Nat.sqrt_pos.mpr hm
  have hi0 := hN.trans_le hi
  have hr : 0 < Real.sqrt (i:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hi0)
  have hn : 0 < Real.sqrt (m.sqrt:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hnr := Real.sqrt_le_sqrt (show (m.sqrt:ℝ) ≤ i by exact_mod_cast hi)
  have hcell : Real.sqrt i * BiarithmeticGaugeGeometry.logCellWidth i ≤ 1 / Real.sqrt i := calc
    _ ≤ Real.sqrt i * (1/(i:ℝ)) := mul_le_mul_of_nonneg_left
      (BiarithmeticGaugeGeometry.logCellWidth_le_inv hi0) hr.le
    _ = _ := by field_simp; exact Real.sq_sqrt (Nat.cast_nonneg i)
  have hweight : (C:ℝ) / Real.sqrt i ≤ (C:ℝ) / Real.sqrt m.sqrt :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg C) hn hnr
  have hf (z : ℝ) (hz : |z| ≤ (C:ℝ) / Real.sqrt m.sqrt) :
      ⌊(m:ℝ)*z⌋.natAbs ≤ meshJetOrder C m := by
    have hab : |(m:ℝ)*z| ≤ (C:ℝ)*m / Real.sqrt m.sqrt := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _), mul_comm (C:ℝ), mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg m)
    have hceil := Nat.le_ceil ((C:ℝ)*m / Real.sqrt m.sqrt)
    rw [← Nat.cast_le (α := ℝ), Nat.cast_natAbs, Int.cast_abs, meshJetOrder, Nat.cast_add, Nat.cast_one, abs_le]
    constructor
    · linarith only [Int.lt_floor_add_one ((m:ℝ)*z), (abs_le.mp hab).1, hceil]
    · linarith only [Int.floor_le ((m:ℝ)*z), (abs_le.mp hab).2, hceil]
  constructor
  · apply hf
    rw [abs_mul, abs_of_nonneg (mul_nonneg hr.le (BiarithmeticGaugeGeometry.logCellWidth_pos hi0).le)]
    exact (mul_le_mul hcell hx (abs_nonneg _) (by positivity)).trans
      ((show (1/Real.sqrt i)*(C:ℝ) = C / Real.sqrt i by ring).le.trans hweight)
  · apply hf
    rw [abs_div, abs_of_nonneg hr.le]
    exact (div_le_div_of_nonneg_right hy hr.le).trans hweight

/-- One exponent bounds both the common denominator and the sum of selectors. -/
def meshJetLogBound (B C m : ℕ) : ℝ :=
  let s := (B+1)*m.sqrt
  (2*meshJetOrder C m*s*(s+1)+1 : ℕ) * Real.log (2*(1+(s:ℝ)^2))

private theorem jet_mesh_atTop : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop.mpr fun n => (eventually_ge_atTop (n*n)).mono fun _ h => Nat.le_sqrt.mpr h

private theorem log_sqrt_decay (A : ℝ) :
    Tendsto (fun m : ℕ => (A+2*Real.log (m.sqrt:ℝ)) / Real.sqrt m.sqrt) atTop (𝓝 0) := by
  have ht : Tendsto (fun m : ℕ => (m.sqrt:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp jet_mesh_atTop
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/2)).tendsto_div_nhds_zero
  have hl' : Tendsto (fun m : ℕ => Real.log (m.sqrt:ℝ) / Real.sqrt m.sqrt) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_eq_rpow] using hl.comp ht
  have hc := tendsto_const_nhds (x := A) (f := (atTop : Filter ℕ))
  have hA : Tendsto (fun m : ℕ => A / Real.sqrt m.sqrt) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Pi.inv_apply, div_eq_mul_inv, mul_zero] using
      hc.mul ((Real.tendsto_sqrt_atTop.comp ht).inv_tendsto_atTop)
  simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using hA.add (hl'.const_mul 2)

private theorem jet_cost_bound (B C m : ℕ) (hm : 0 < m) :
    meshJetLogBound B C m / (m:ℝ)^2 ≤
      (2*((C:ℝ)+2)*(B+1)*(B+2)+1) *
        ((Real.log (4*((B:ℝ)+1)^2)+2*Real.log (m.sqrt:ℝ)) / Real.sqrt m.sqrt) := by
  let n : ℝ := m.sqrt
  let b : ℝ := (B:ℝ)+1
  let s : ℝ := b*n
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ m.sqrt from Nat.sqrt_pos.mpr hm)
  have hn0 : 0 < n := by linarith
  have hm' : 1 ≤ (m:ℝ) := by exact_mod_cast hm
  have hn2 : n^2 ≤ (m:ℝ) := by dsimp [n]; rw [sq]; exact_mod_cast Nat.sqrt_le m
  have hb : 1 ≤ b := by dsimp [b]; linarith only [Nat.cast_nonneg (α := ℝ) B]
  have hs : 1 ≤ s := one_le_mul_of_one_le_of_one_le hb hn
  have hr : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hrn : Real.sqrt n ≤ n := by
    nlinarith only [Real.sq_sqrt hn0.le, mul_nonneg (sub_nonneg.mpr (Real.one_le_sqrt.mpr hn))
      (Real.sqrt_nonneg n)]
  have hrm : Real.sqrt n ≤ (m:ℝ) :=
    hrn.trans ((by nlinarith only [mul_nonneg (sub_nonneg.mpr hn) hn0.le] : n ≤ n^2).trans hn2)
  have hh : (meshJetOrder C m:ℝ)*Real.sqrt n ≤ ((C:ℝ)+2)*m := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ (C:ℝ)*m / Real.sqrt n by positivity)
    change ((⌈(C:ℝ)*m / Real.sqrt n⌉₊+1 : ℕ):ℝ)*Real.sqrt n ≤ _
    push_cast
    have hh := (lt_div_iff₀ hr).mp (show (⌈(C:ℝ)*m / Real.sqrt n⌉₊:ℝ)-1 <
      (C:ℝ)*m / Real.sqrt n by linarith only [h])
    linarith only [hh, hrm]
  have hss : s*(s+1) ≤ b*(b+1)*m := calc
    _ ≤ (b*n)*((b+1)*n) := mul_le_mul_of_nonneg_left (by dsimp [s]; linarith only [hn]) (by positivity)
    _ = b*(b+1)*n^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn2 (by positivity)
  have hmain := mul_le_mul hh hss (by positivity) (by positivity)
  have hrr : Real.sqrt n ≤ (m:ℝ)^2 := hrm.trans (by nlinarith only [mul_nonneg (sub_nonneg.mpr hm') (Nat.cast_nonneg (α := ℝ) m)])
  have hexp : ((2*(meshJetOrder C m:ℝ)*s*(s+1)+1) / (m:ℝ)^2) ≤
      (2*((C:ℝ)+2)*b*(b+1)+1) / Real.sqrt n := by
    rw [div_le_div_iff₀ (by positivity) hr]
    nlinarith only [hmain, hrr]
  have hlog : Real.log (2*(1+s^2)) ≤ Real.log (4*b^2)+2*Real.log n := by
    have hlog2 : 2 * Real.log n = Real.log (n^2) := by simp [Real.log_pow]
    rw [hlog2, ← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    dsimp only [s] at *
    nlinarith only [sq_nonneg (b*n-1), hs]
  have hlog0 : 0 ≤ Real.log (2*(1+s^2)) := Real.log_nonneg (by nlinarith only [sq_nonneg s])
  have hh' := mul_le_mul hexp hlog hlog0 (by positivity)
  dsimp only [meshJetLogBound]
  push_cast
  dsimp only [s,b,n] at hh'
  ring_nf at hh' ⊢
  exact hh'

/-- Uniform bidisk log cost of clearing and lifting every jet on a fixed
ratio window is subquadratic along all integer dilations. -/
theorem meshJetLogBound_subquadratic (B C : ℕ) :
    Tendsto (fun m : ℕ => meshJetLogBound B C m / (m:ℝ)^2) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun m => ?_)
    ((eventually_ge_atTop 1).mono fun m hm => jet_cost_bound B C m hm)
  · simpa only [mul_zero] using
      (log_sqrt_decay (Real.log (4*((B:ℝ)+1)^2))).const_mul (2*((C:ℝ)+2)*(B+1)*(B+2)+1)
  · unfold meshJetLogBound
    apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg _)
    nlinarith only [sq_nonneg (((B+1)*m.sqrt:ℕ):ℝ)]

/-- All branch data of bidisk norm at most one lift with the same multiplier
and log budget. The congruences hold in the integral polynomial ring. -/
theorem conductorMeshJetSections (B C m : ℕ) (data : ℕ → Polynomial ℤ[X]) :
    let S := Icc (max 1 m.sqrt) (B*m.sqrt)
    let h := meshJetOrder C m
    ∃ (D : ℤ[X]) (F : Polynomial ℤ[X]), D ≠ 0 ∧
      (∀ j ∈ S, (X - Polynomial.C (conductorGraph j))^h ∣ F - Polynomial.C D * data j) ∧
      (verticalContent D : ℝ) ≤ Real.exp (meshJetLogBound B C m) ∧
      ∀ e : Polynomial ℤ[X] →+* ℂ, ‖e X‖ ≤ 1 → ‖e (Polynomial.C X)‖ ≤ 1 →
        (∀ j ∈ S, ‖e (data j)‖ ≤ 1) →
        max ‖e (Polynomial.C D)‖ ‖e F‖ ≤ Real.exp (meshJetLogBound B C m) := by
  intro S h
  let s := (B+1)*m.sqrt
  have hs : S.card ≤ s := by
    dsimp [S]
    rw [Nat.card_Icc]
    dsimp [s]
    rw [Nat.add_mul, Nat.one_mul]
    have := Nat.le_max_left 1 m.sqrt
    omega
  have hS : 0 ∉ S := by simp [S]
  have hindex (i) (hi : i ∈ S) : 0 < i ∧ i ≤ s := by
    obtain ⟨hl,hu⟩ := mem_Icc.mp hi
    exact ⟨(Nat.le_max_left 1 m.sqrt).trans hl, hu.trans
      (Nat.mul_le_mul_right _ (Nat.le_succ B))⟩
  let U : ℝ := 2*(1+(s:ℝ)^2)
  have hU : 1 ≤ U := by dsimp [U]; nlinarith only [sq_nonneg (s:ℝ)]
  have hsU : (s:ℝ)+1 ≤ U := by dsimp [U]; nlinarith only [sq_nonneg ((s:ℝ)-1)]
  have hsc : (S.card:ℝ) ≤ U := (by exact_mod_cast hs : (S.card:ℝ) ≤ s).trans
    ((le_add_of_nonneg_right zero_le_one).trans hsU)
  have hbound : Real.exp (meshJetLogBound B C m) = U^(2*h*s*(s+1))*U := by
    change Real.exp (((2*h*s*(s+1)+1 : ℕ):ℝ)*Real.log U) = _
    rw [mul_comm _ (Real.log U), ← Real.rpow_def_of_pos (zero_lt_one.trans_le hU), Real.rpow_natCast, pow_succ]
  refine ⟨_, _, conductorJetMultiplier_ne_zero S h hS, fun j hj =>
    graphJetSection_restrict S conductorGraph h data hj, ?_, ?_⟩
  · rw [hbound]
    have hc := conductorJetMultiplier_content_le S h (s+1) (Nat.succ_pos _) fun i hi =>
      ⟨(hindex _ hi).1, (hindex _ hi).2.trans (Nat.le_succ s)⟩
    have hc' : (verticalContent (graphJetMultiplier S conductorGraph h):ℝ) ≤
        ((s:ℝ)+1)^(2*h*S.card*S.card) := by exact_mod_cast hc
    refine hc'.trans ((pow_le_pow_left₀ (by positivity) hsU _).trans ?_)
    apply (pow_le_pow_right₀ hU (show 2*h*S.card*S.card ≤ 2*h*s*(s+1) from Nat.mul_le_mul
      (Nat.mul_le_mul_left _ hs) (hs.trans (Nat.le_succ s)))).trans
    exact le_mul_of_one_le_right (by positivity) hU
  intro e hY hT hdata
  have hg (i) (hi : i ∈ S) : ‖e (Polynomial.C (conductorGraph i))‖ ≤ (s:ℝ)^2 := by
    apply (graph_disk_bound (e.comp Polynomial.C) hT i).trans
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast (hindex _ hi).2
  obtain ⟨hD,hF⟩ := graphJetSection_norm S conductorGraph h data e (sq_nonneg _) zero_le_one hY hg hdata
  have hx : 2*h*S.card*(S.card+1) ≤ 2*h*s*(s+1) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hs)
    (Nat.succ_le_succ hs)
  have hpow := pow_le_pow_right₀ hU hx
  rw [hbound]
  apply max_le
  · exact (hD.trans hpow).trans (le_mul_of_one_le_right (by positivity) hU)
  · rw [mul_one] at hF
    exact hF.trans ((mul_le_mul hsc hpow (by positivity) (by positivity)).trans_eq (mul_comm _ _))

#print axioms meshJetLogBound_subquadratic
#print axioms conductorMeshJetSections

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
