import GaloisForLFunctions.RHTower.ChiRamanujanRationalCubicTrace
import GaloisForLFunctions.RHTower.ChiRamanujanWeightedCubicContractions

/-!
# Full weighted positive-rational cubic and both contraction transforms

Every imaginary Mellin frequency is retained in the complete unordered
rational sum. Its exact absolute mass is the balanced mass, and support
exhaustion identifies its value with the six-zeta source. Both literal
rational axes have their complete two-zeta transforms.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RHTower.BAGTrace

def complexPrimeSupportCut {α X : Type} [Zero X] (f : (α →₀ X) → ℂ)
    (P : Finset α) : (α →₀ X) → ℂ := {v | v.support ⊆ P}.indicator f

theorem tendsto_tsum_complexPrimeSupportCut {α X : Type} [Zero X]
    {f : (α →₀ X) → ℂ} (hf : Summable (fun v => ‖f v‖)) :
    Tendsto (fun P : Finset α => ∑' v,complexPrimeSupportCut f P v) atTop (𝓝 (∑' v,f v)) := by
  classical
  apply tendsto_tsum_of_dominated_convergence hf
  · intro v
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop v.support] with P hP
    simp [complexPrimeSupportCut,hP]
  · exact Eventually.of_forall fun P v => by
      by_cases h : v.support ⊆ P <;> simp [complexPrimeSupportCut,h]

theorem complex_finite_finsupp_product_hasSum {α X : Type} [AddCommMonoid X]
    (P : Finset α) (f : α → X → ℂ) (L : α → ℂ)
    (hf0 : ∀ p,f p 0=1) (hlocal : ∀ p,HasSum (f p) (L p)) :
    HasSum (complexPrimeSupportCut (fun v : α →₀ X => v.prod f) P) (∏ p ∈ P,L p) := by
  classical
  have h := complex_finite_product_hasSum P (fun p => f p) (fun p => L p) (fun p => hlocal p)
  have hs := ((supportedCoordinates (X := X) P).hasSum_iff).mpr h
  have hs' : HasSum (fun v : {v : α →₀ X // v.support ⊆ P} => v.1.prod f)
      (∏ p : P,L p) := by
    apply hs.congr_fun
    intro v
    rw [v.1.prod_of_support_subset v.2 f (fun p _ => hf0 p)]
    exact (Finset.prod_coe_sort P (fun p => f p (v.1 p))).symm
  rw [Finset.prod_coe_sort] at hs'
  exact hasSum_subtype_iff_indicator.mp hs'

theorem cubicPrimeBase_ofReal (p : Nat.Primes) (σ : ℝ) :
    cubicPrimeBase p (σ : ℂ) = (primeWeight σ p : ℂ) := by
  rw [primeWeight,Complex.ofReal_cpow (by exact_mod_cast p.property.pos.le)]
  simp only [cubicPrimeBase,Complex.ofReal_neg,Complex.ofReal_natCast]

theorem norm_weightedLocal_imag (σ : ℝ) {α β : ℂ} (hα : α.re=0) (hβ : β.re=0)
    (p : Nat.Primes) (v : ℤ × ℤ) :
    ‖weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p ((σ : ℂ)+α))
      (cubicPrimeBase p ((σ : ℂ)+β)) v‖ = |localTriple (primeWeight σ p) v| := by
  have hx : ‖cubicPrimeBase p ((σ : ℂ)+α)‖ = ‖cubicPrimeBase p σ‖ := by
    simp only [norm_cubicPrimeBase,Complex.add_re,Complex.ofReal_re,hα,add_zero]
  have hy : ‖cubicPrimeBase p ((σ : ℂ)+β)‖ = ‖cubicPrimeBase p σ‖ := by
    simp only [norm_cubicPrimeBase,Complex.add_re,Complex.ofReal_re,hβ,add_zero]
  calc
    _ = ‖weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p σ) (cubicPrimeBase p σ) v‖ := by
      simp only [weightedLocal,norm_mul,norm_zpow,hx,hy]
    _ = _ := by
      rw [cubicPrimeBase_ofReal,weightedLocal_balanced (primeWeight_pos σ p).ne']
      exact Complex.norm_real _

def weightedValuationCubic (σ : ℝ) (α β : ℂ) (v : Nat.Primes →₀ ℤ × ℤ) : ℂ :=
  v.prod (fun p => weightedLocal (cubicPrimeBase p σ)
    (cubicPrimeBase p ((σ : ℂ)+α)) (cubicPrimeBase p ((σ : ℂ)+β)))

theorem norm_weightedValuationCubic (σ : ℝ) {α β : ℂ}
    (hα : α.re=0) (hβ : β.re=0) (v : Nat.Primes →₀ ℤ × ℤ) :
    ‖weightedValuationCubic σ α β v‖ = |valuationCubic σ v| := by
  simp only [weightedValuationCubic,valuationCubic,Finsupp.prod,norm_prod,
    norm_weightedLocal_imag σ hα hβ,Finset.abs_prod]

def sixZetaCubic (σ α β : ℂ) : ℂ :=
  cubicEulerCorrection σ α β *
    ((riemannZeta (σ+(β-α)))⁻¹ * (riemannZeta (σ+(α-β)))⁻¹) *
    riemannZeta (σ+α) * riemannZeta (σ+β) * riemannZeta (σ-α) * riemannZeta (σ-β)

theorem weightedValuationCubic_hasSum {σ : ℝ} (hσ : 1 < σ) {α β : ℂ}
    (hα : α.re=0) (hβ : β.re=0) :
    HasSum (weightedValuationCubic σ α β) (sixZetaCubic σ α β) := by
  have hn : Summable (fun v => ‖weightedValuationCubic σ α β v‖) := by
    simpa only [norm_weightedValuationCubic σ hα hβ] using (valuationCubic_abs_hasSum hσ).summable
  have hpos (s : ℂ) (hs : s.re=0) : 0 < ((σ : ℂ)+s).re := by
    simp only [Complex.add_re,Complex.ofReal_re,hs,add_zero]
    linarith
  have hnorm (p : Nat.Primes) (s : ℂ) (hs : s.re=0) :
      ‖cubicPrimeBase p ((σ : ℂ)+s)‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt)
      (neg_neg_of_pos (hpos s hs))
  have hc (P : Finset Nat.Primes) :
      HasSum (complexPrimeSupportCut (weightedValuationCubic σ α β) P)
        (weightedTrace σ α β P) := by
    rw [weightedTrace_eq (hpos α hα) (hpos β hβ)]
    exact complex_finite_finsupp_product_hasSum P _ _
      (fun p => by simp [weightedLocal,complexCoefficient])
      (fun p => weightedLocal_hasSum _ (hnorm p α hα) (hnorm p β hβ))
  have hlim := tendsto_tsum_complexPrimeSupportCut hn
  have he : (∑' v,weightedValuationCubic σ α β v)=sixZetaCubic σ α β := by
    apply tendsto_nhds_unique hlim
    simpa only [(hc _).tsum_eq,sixZetaCubic] using
      complete_weighted_trace_six_zeta (σ := (σ : ℂ)) (by simpa using hσ) hα hβ
  rw [← he]
  exact hn.of_norm.hasSum

private theorem cpow_real_prime_zpow (p : Nat.Primes) (i : ℤ) (s : ℂ) :
    (((p : ℝ)^i : ℝ) : ℂ)^(-s) = cubicPrimeBase p s^i := by
  rw [Complex.ofReal_zpow,Complex.ofReal_natCast,
    ← Complex.cpow_int_mul' (by simp [Complex.natCast_arg,Real.pi_pos])
      (by simp [Complex.natCast_arg,Real.pi_pos.le])]
  exact Complex.cpow_int_mul _ _ _

private theorem cpow_real_prime_product (P : Finset Nat.Primes) (v : Nat.Primes → ℤ) (s : ℂ) :
    ((∏ p ∈ P,(p : ℝ)^(v p) : ℝ) : ℂ)^(-s) = ∏ p ∈ P,cubicPrimeBase p s^(v p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    rw [Finset.prod_insert hp,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (zpow_pos (by exact_mod_cast p.property.pos) _).le
        (Finset.prod_pos (fun q _ => zpow_pos (by exact_mod_cast q.property.pos) _)).le,
      cpow_real_prime_zpow,ih,Finset.prod_insert hp]

theorem cpow_rationalOfValuations (s : ℂ) (v : PrimeValuations) :
    (rationalOfValuations v : ℂ)^(-s) = v.prod (fun p i => cubicPrimeBase p s^i) := by
  have he : (rationalOfValuations v : ℂ)=((∏ p ∈ v.support,(p : ℝ)^(v p) : ℝ) : ℂ) := by
    simp [rationalOfValuations,Finsupp.prod]
  rw [he]
  exact cpow_real_prime_product v.support v s

def rationalCharacter (α : ℂ) (a : PositiveRational) : ℂ := (a.1 : ℂ)^(-α)

theorem norm_rationalCharacter {α : ℂ} (hα : α.re=0) (a : PositiveRational) :
    ‖rationalCharacter α a‖=1 := by
  change ‖((a.1 : ℝ) : ℂ)^(-α)‖=1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast a.2)]
  simp only [Complex.neg_re,hα,neg_zero,Real.rpow_zero]

def weightedRationalCubic (σ : ℝ) (α β : ℂ) (w : PositiveRational × PositiveRational) : ℂ :=
  (rationalCubic σ w : ℂ)*rationalCharacter α w.1*rationalCharacter β w.2

theorem norm_weightedRationalCubic (σ : ℝ) {α β : ℂ} (hα : α.re=0) (hβ : β.re=0)
    (w : PositiveRational × PositiveRational) :
    ‖weightedRationalCubic σ α β w‖=|rationalCubic σ w| := by
  simp only [weightedRationalCubic,norm_mul,norm_rationalCharacter hα,
    norm_rationalCharacter hβ,mul_one,Complex.norm_real,Real.norm_eq_abs]

theorem weightedLocal_twist (p : Nat.Primes) (σ : ℝ) (α β : ℂ) (v : ℤ × ℤ) :
    weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p ((σ : ℂ)+α))
      (cubicPrimeBase p ((σ : ℂ)+β)) v =
    (localTriple (primeWeight σ p) v : ℂ)*cubicPrimeBase p α^v.1*cubicPrimeBase p β^v.2 := by
  rw [← cubicPrimeBase_mul,← cubicPrimeBase_mul]
  simp only [weightedLocal,mul_zpow]
  have h := weightedLocal_balanced (primeWeight_pos σ p).ne' v
  rw [← cubicPrimeBase_ofReal] at h
  simp only [weightedLocal] at h
  rw [← h]
  ring

theorem weightedRationalCubic_equiv (σ : ℝ) (α β : ℂ) (v : Nat.Primes →₀ ℤ × ℤ) :
    weightedRationalCubic σ α β (positiveRationalPairEquiv v)=weightedValuationCubic σ α β v := by
  classical
  let u := (valuationPairEquiv v).1
  let w := (valuationPairEquiv v).2
  have hu : u.support ⊆ v.support := Finsupp.support_mapRange (hf := rfl)
  have hw : w.support ⊆ v.support := Finsupp.support_mapRange (hf := rfl)
  have hchar (s : ℂ) (a : PrimeValuations) :
      rationalCharacter s (positiveRationalEquiv a) = a.prod (fun p i => cubicPrimeBase p s^i) :=
    cpow_rationalOfValuations s a
  rw [weightedRationalCubic,rationalCubic_equiv]
  change (valuationCubic σ v : ℂ)*rationalCharacter α (positiveRationalEquiv u)*
    rationalCharacter β (positiveRationalEquiv w)=_
  rw [hchar,hchar,u.prod_of_support_subset hu _ (fun p _ => zpow_zero _),
    w.prod_of_support_subset hw _ (fun p _ => zpow_zero _)]
  simp only [valuationCubic,weightedValuationCubic,Finsupp.prod,Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  exact (weightedLocal_twist p σ α β (v p)).symm

/-- The complete unordered actual rational cubic equals the six-zeta trace at every frequency. -/
theorem weightedRationalCubic_hasSum {σ : ℝ} (hσ : 1 < σ) {α β : ℂ}
    (hα : α.re=0) (hβ : β.re=0) :
    HasSum (weightedRationalCubic σ α β) (sixZetaCubic σ α β) := by
  have h := (weightedValuationCubic_hasSum hσ hα hβ).congr_fun
    (fun v => weightedRationalCubic_equiv σ α β v)
  exact positiveRationalPairEquiv.hasSum_iff.mp h

theorem weightedRationalCubic_norm_hasSum {σ : ℝ} (hσ : 1 < σ) {α β : ℂ}
    (hα : α.re=0) (hβ : β.re=0) :
    HasSum (fun w => ‖weightedRationalCubic σ α β w‖)
      ((riemannZeta (σ : ℂ)).re^2 * ∏' p,(1+4*primeWeight σ p)) := by
  exact (rationalCubic_abs_hasSum hσ).congr_fun (norm_weightedRationalCubic σ hα hβ)

def weightedValuationAxis (σ : ℝ) (α : ℂ) (v : PrimeValuations) : ℂ :=
  v.prod (fun p i => weightedLocal (cubicPrimeBase p σ)
    (cubicPrimeBase p ((σ : ℂ)+α)) (cubicPrimeBase p σ) (i,0))

private theorem localTriple_axis_dilation (z : ℝ) (i : ℤ) :
    localTriple z (i,0)=localDilation z 0 i := by
  simp only [localTriple,localDilation,add_zero,
    show coefficient z 0=1 by simp [coefficient],mul_one]

theorem norm_weightedValuationAxis (σ : ℝ) {α : ℂ} (hα : α.re=0) (v : PrimeValuations) :
    ‖weightedValuationAxis σ α v‖=valuationEnergy σ v := by
  calc
    _ = |valuationEnergy σ v| := by
      rw [valuationEnergy_prod]
      simp only [weightedValuationAxis,Finsupp.prod,norm_prod,Finset.abs_prod]
      apply Finset.prod_congr rfl
      intro p hp
      simpa only [Complex.zero_re,add_zero,localTriple_axis_dilation] using
        norm_weightedLocal_imag σ hα (β := 0) rfl p (v p,0)
    _ = _ := abs_of_nonneg (valuationEnergy_nonneg σ v)

def twoZetaAxis (σ α : ℂ) : ℂ :=
  axisEulerCorrection σ α*riemannZeta (σ+α)*riemannZeta (σ-α)

theorem weightedValuationAxis_hasSum {σ : ℝ} (hσ : 1 < σ) {α : ℂ} (hα : α.re=0) :
    HasSum (weightedValuationAxis σ α) (twoZetaAxis σ α) := by
  have hn : Summable (fun v => ‖weightedValuationAxis σ α v‖) := by
    simpa only [norm_weightedValuationAxis σ hα] using (valuationEnergy_hasSum hσ).summable
  have hpos : 0 < ((σ : ℂ)+α).re := by
    simp only [Complex.add_re,Complex.ofReal_re,hα,add_zero]
    linarith
  have hnorm (p : Nat.Primes) : ‖cubicPrimeBase p ((σ : ℂ)+α)‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt)
      (neg_neg_of_pos hpos)
  have hc (P : Finset Nat.Primes) :
      HasSum (complexPrimeSupportCut (weightedValuationAxis σ α) P)
        (weightedAxisTrace σ α P) := by
    rw [weightedAxisTrace_eq hpos]
    exact complex_finite_finsupp_product_hasSum P _ _
      (fun p => by simp [weightedLocal,complexCoefficient])
      (fun p => weightedAxis_hasSum _ _ (hnorm p))
  have hlim := tendsto_tsum_complexPrimeSupportCut hn
  have he : (∑' v,weightedValuationAxis σ α v)=twoZetaAxis σ α := by
    apply tendsto_nhds_unique hlim
    simpa only [(hc _).tsum_eq,twoZetaAxis] using
      complete_weighted_axis_two_zeta (σ := (σ : ℂ)) (by simpa using hσ) hα
  rw [← he]
  exact hn.of_norm.hasSum

def weightedRationalAxis (σ : ℝ) (α : ℂ) (a : PositiveRational) : ℂ :=
  (rationalDilation σ rationalOne a : ℂ)*rationalCharacter α a

theorem weightedRationalAxis_equiv (σ : ℝ) (α : ℂ) (v : PrimeValuations) :
    weightedRationalAxis σ α (positiveRationalEquiv v)=weightedValuationAxis σ α v := by
  have he : positiveRationalValuations rationalOne=0 :=
    (positiveRationalValuations_eq_zero_iff rationalOne).mpr rfl
  have hchar : rationalCharacter α (positiveRationalEquiv v)=
      v.prod (fun p i => cubicPrimeBase p α^i) := cpow_rationalOfValuations α v
  rw [weightedRationalAxis,rationalDilation_eq_valuation,he,positiveRationalValuations_equiv,hchar]
  have hv : valuationDilation σ 0 v=valuationEnergy σ v := by
    simp only [valuationDilation,valuationEnergy,add_zero,pow_two]
  rw [hv,valuationEnergy_prod]
  simp only [weightedValuationAxis,Finsupp.prod,Complex.ofReal_prod,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  simpa only [add_zero,localTriple_axis_dilation,zpow_zero,mul_one] using
    (weightedLocal_twist p σ α 0 (v p,0)).symm

theorem weightedRationalAxis_hasSum {σ : ℝ} (hσ : 1 < σ) {α : ℂ} (hα : α.re=0) :
    HasSum (weightedRationalAxis σ α) (twoZetaAxis σ α) := by
  have h := (weightedValuationAxis_hasSum hσ hα).congr_fun (weightedRationalAxis_equiv σ α)
  exact positiveRationalEquiv.hasSum_iff.mp h

end RHTower.BAGTrace
