import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.Capture
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.SpectralEdge.IndependentFields.Moments.CircuitTrace
import GaloisForLFunctions.HTGeometry.GaussianSmallBallLowerBound
import GaloisForLFunctions.HTGeometry.TorsionPolygonRecurrenceShadowing

/-! # A floor at every order for unsigned local-slope moments -/

open Finset Set MeasureTheory ProbabilityTheory Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
noncomputable section

/-- Every displacement in a small Gaussian cube keeps the identity twist
above the given overlap threshold. Its mass survives normalization by the
threshold power at every replica order and for every input distribution. -/
theorem slope_moment_identity_floor {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i=1)
    (v : J → I → ℝ) (hv : ∀ l i, |v l i| ≤ 1) (q : ℕ)
    {τ η L : ℝ} (hτ : 0 ≤ τ) (hbox : Fintype.card J*η*|L| ≤ 1-τ) :
    τ^(2*q)*((gaussianReal 0 1).real (Icc (-η) η))^Fintype.card J ≤ slopeMoment w v q L := by
  let μ := Measure.pi fun _ : J => gaussianReal 0 1
  let C := {g : J → ℝ | ∀ l, |g l| ≤ η}
  let A := {g : J → ℝ | τ ≤ ‖twistedFiniteSpectralAmplitude w (fieldEnergy v g) (fun _ => 1) L‖}
  have hmass : ((gaussianReal 0 1).real (Icc (-η) η))^Fintype.card J = μ.real C := by
    have hc : C=Set.univ.pi (fun _ : J => Icc (-η) η) := by
      ext g
      simp only [C,mem_setOf_eq,mem_univ_pi,Set.mem_Icc,abs_le]
    simp only [hc,μ,Measure.real,Measure.pi_pi,prod_const,card_univ,ENNReal.toReal_pow]
  have hsub : C ⊆ A := by
    intro g hg
    let E := fieldEnergy v g
    let f (i : I) := Complex.exp (((E i*L:ℝ):ℂ)*Complex.I)
    have hE (i : I) : |E i| ≤ Fintype.card J*η := by
      apply (abs_sum_le_sum_abs ..).trans
      have h (l : J) : |g l*v l i| ≤ η := by
        rw [abs_mul]
        exact (mul_le_of_le_one_right (abs_nonneg _) (hv l i)).trans (hg l)
      simpa only [sum_const,card_univ,nsmul_eq_mul] using sum_le_sum (s:=univ) (fun l _ => h l)
    have hf (i : I) : ‖f i-1‖ ≤ 1-τ := by
      have h := norm_exp_ofReal_mul_I_sub_le (E i*L) 0
      simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,sub_zero,abs_mul] at h
      exact h.trans ((mul_le_mul_of_nonneg_right (hE i) (abs_nonneg L)).trans hbox)
    have hs : (∑ i, (w i:ℂ))=1 := by exact_mod_cast hsum
    let S := ∑ i, (w i:ℂ)*f i
    have hdist : ‖S-1‖ ≤ 1-τ := by
      rw [←hs,show S-∑ i, (w i:ℂ)=∑ i, (w i:ℂ)*(f i-1) by
        simp only [S,mul_sub,mul_one,sum_sub_distrib]]
      apply (norm_sum_le ..).trans
      calc
        _ ≤ ∑ i, w i*(1-τ) := sum_le_sum fun i _ => by
          rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (hw i)]
          exact mul_le_mul_of_nonneg_left (hf i) (hw i)
        _ = _ := by rw [←sum_mul,hsum,one_mul]
    have ht := norm_sub_norm_le (1:ℂ) S
    rw [norm_one,norm_sub_rev] at ht
    change τ ≤ ‖twistedFiniteSpectralAmplitude w E (fun _ => 1) L‖
    simp only [twistedFiniteSpectralAmplitude,mul_one]
    change τ ≤ ‖S‖
    linarith only [hdist,ht]
  have hm := field_capture_moment w hw hsum v (fun (_ : Unit) (_ : I) => (1:ℂ))
    (fun _ _ => norm_one.le) q L hτ
  have hu : (⋃ _ : Unit, A)=A := by
    ext g
    constructor
    · intro h
      obtain ⟨_,hg⟩ := mem_iUnion.mp h
      exact hg
    · exact fun hg => mem_iUnion.mpr ⟨(),hg⟩
  change τ^(2*q)*μ.real (⋃ _ : Unit, A) ≤ (Fintype.card Unit:ℝ)*slopeMoment w v q L at hm
  have ha : τ^(2*q)*μ.real A ≤ slopeMoment w v q L := by simpa [hu] using hm
  exact (mul_le_mul_of_nonneg_left (hmass.le.trans (measureReal_mono hsub)) (pow_nonneg hτ _)).trans ha

/-- Even after choosing the tested energy levels, their weights and the
order, an unsigned estimate multiplied by the full circuit entropy retains
the same Gaussian cube. The lower bound holds on every physical base. -/
theorem unsigned_circuit_price_floor (n s : ℕ) (h : Coeff n) (R : Finset (Fin (n+2) → Bool))
    (w : R → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j=1) (q : ℕ)
    {τ η L : ℝ} (hτ : 0<τ) (hη : η∈Icc (0:ℝ) 1) (hbox : Fintype.card (PathLabel n)*η*|L| ≤ 1-τ) :
    let m := Fintype.card (PathLabel n)
    let J := atMostQuarterCircuitEntropyBound (n+2) s
    let v (l : PathLabel n) (j : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h) l j.val
    J*(gaussianDensityFloor*(2*η))^m ≤ J*slopeMoment w v q L/τ^(2*q) := by
  intro m J v
  let U := (generator h).2.isHermitian.eigenvectorUnitary
  have hv (l : PathLabel n) (j : R) : |v l j| ≤ 1 := by
    let P := finitePauliMatrix (pathWord l)
    apply (Complex.abs_re_le_norm ((U.valᴴ*P*U.val) j.val j.val)).trans
    apply (norm_entry_le_l2_opNorm _ j.val j.val).trans
    rw [CStarRing.norm_mul_mem_unitary _ U.2,←Matrix.star_eq_conjTranspose,
      CStarRing.norm_mem_unitary_mul _ (Unitary.star_mem U.2),show ‖P‖=1 from norm_finitePauliMatrix _]
  have hc : 0 ≤ gaussianDensityFloor*(2*η) := mul_nonneg gaussianDensityFloor_pos.le (by linarith only [hη.1])
  have hb := ENNReal.toReal_mono (measure_ne_top _ _) (gaussianReal_Icc_lower hη.2)
  rw [ENNReal.toReal_ofReal hc] at hb
  have hpow := pow_le_pow_left₀ hc hb m
  have h := (mul_le_mul_of_nonneg_left hpow (pow_nonneg hτ.le (2*q))).trans
    (slope_moment_identity_floor w hw hsum v hv q hτ.le hbox)
  have hJ : 0 ≤ J := (Nat.cast_nonneg _).trans (atMostQuarterCircuitNet_card_real_le ..)
  apply (le_div_iff₀ (pow_pos hτ (2*q))).mpr
  rw [mul_assoc,mul_comm ((gaussianDensityFloor*(2*η))^m)]
  exact mul_le_mul_of_nonneg_left h hJ

/-- The last architecture-length summand alone is at least two to the
gate count on every physical register. -/
theorem circuit_entropy_price_lower (n s : ℕ) :
    (2:ℝ)^s ≤ atMostQuarterCircuitEntropyBound (n+2) s := by
  let B : ℝ := ((n+2)*(n+2):ℕ)
  have hB : 2 ≤ B := by
    dsimp only [B]
    push_cast
    nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
  have hpow : 1 ≤ (1+16*(s:ℝ))^(32*s) := one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  calc
    (2:ℝ)^s ≤ B^s := pow_le_pow_left₀ (by norm_num) hB _
    _ ≤ B^s*(1+16*(s:ℝ))^(32*s) := le_mul_of_one_le_right (by positivity) hpow
    _ ≤ 1+B^s*(1+16*(s:ℝ))^(32*s) := le_add_of_nonneg_left zero_le_one
    _ ≤ _ := Finset.single_le_sum (f:=fun j : ℕ => 1+B^j*(1+16*(j:ℝ))^(32*j))
      (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self s))

/-- If d bits resolve the entire phase displacement, a budget of
m(d+C) gates makes the unsigned probability estimate at least one. The
constant C is absolute and the conclusion holds at every replica order. -/
theorem unsigned_price_at_dyadic_resolution :
    ∃ C : ℕ, ∀ (n s d q : ℕ) (h : Coeff n) (R : Finset (Fin (n+2) → Bool))
      (w : R → ℝ), (∀ j, 0 ≤ w j) → ∑ j, w j=1 → ∀ {τ L : ℝ}, 0<τ →
      (Fintype.card (PathLabel n):ℝ)*|L| ≤ (1-τ)*2^d →
      (d+C)*Fintype.card (PathLabel n) ≤ s →
      let v (l : PathLabel n) (j : R) := FirstGate.ResponseWeights.localMean (WithLp.toLp 2 h) l j.val
      1 ≤ atMostQuarterCircuitEntropyBound (n+2) s*slopeMoment w v q L/τ^(2*q) := by
  have hg : 0 < 2*gaussianDensityFloor := mul_pos two_pos gaussianDensityFloor_pos
  obtain ⟨C,hC⟩ := pow_unbounded_of_one_lt (1/(2*gaussianDensityFloor)) (by norm_num : (1:ℝ)<2)
  refine ⟨C,?_⟩
  intro n s d q h R w hw hsum τ L hτ hscale hbudget v
  let m := Fintype.card (PathLabel n)
  let η : ℝ := 1/2^d
  let B := gaussianDensityFloor*(2*η)
  have hd : 0 < (2:ℝ)^d := by positivity
  have hη : η∈Icc (0:ℝ) 1 :=
    ⟨(div_pos zero_lt_one hd).le,(div_le_one hd).mpr (one_le_pow₀ one_le_two)⟩
  have hbox : (m:ℝ)*η*|L| ≤ 1-τ := by
    rw [show (m:ℝ)*η*|L|=(m:ℝ)*|L|/2^d by dsimp only [η]; ring]
    exact (div_le_iff₀ hd).mpr hscale
  have hB : 0 ≤ B := mul_nonneg gaussianDensityFloor_pos.le (mul_nonneg (by norm_num) hη.1)
  have hunit : 1 ≤ (2:ℝ)^(d+C)*B := by
    apply ((div_lt_iff₀ hg).mp hC).le.trans_eq
    dsimp only [B,η]
    rw [pow_add]
    field_simp
  have hm : 1 ≤ ((2:ℝ)^(d+C)*B)^m := one_le_pow₀ hunit
  rw [mul_pow,←pow_mul] at hm
  apply hm.trans
  apply le_trans _ (unsigned_circuit_price_floor n s h R w hw hsum q hτ hη hbox)
  exact mul_le_mul_of_nonneg_right
    ((pow_le_pow_right₀ one_le_two hbudget).trans (circuit_entropy_price_lower n s)) (pow_nonneg hB _)

#print axioms slope_moment_identity_floor
#print axioms unsigned_circuit_price_floor
#print axioms circuit_entropy_price_lower
#print axioms unsigned_price_at_dyadic_resolution
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.SpectralEdge
