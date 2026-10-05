import GaloisForLFunctions.RHTower.ChiRamanujanBalancedLabelTrace
import GaloisForLFunctions.RHTower.ChiRamanujanWeightedDistinguishedCubic
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Complete numerator cofactors and the distinguished-source double pole

The two coprime numerator variables are retained through principal-character
Dirichlet series. Their exact continuations and residues combine with the
full two-variable weighted distinguished-label trace. The balanced joint
residue is the explicit negative sum of squares from the signed trace,
multiplied by two further prime-normalization factors.

The mixed valuation/cofactor source has an absolute HasSum in the two open
Dirichlet half planes. Its joint residue is unconditional for every finite
prime set. Rational reindexing to the entire denominator-restricted grid,
and cancellation after pairing with the actual growing physical profile,
remain separate mathematical obligations. No RH proof is claimed.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RHTower.BAGTrace

def criticalPrimeLevel (P : Finset Nat.Primes) : ℕ := ∏ p ∈ P, (p : ℕ)

private lemma level_ne_zero (P : Finset Nat.Primes) : criticalPrimeLevel P ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun p _ => p.property.ne_zero)

private instance (P : Finset Nat.Primes) : NeZero (criticalPrimeLevel P) := ⟨level_ne_zero P⟩

private lemma level_primeFactors (P : Finset Nat.Primes) :
    (criticalPrimeLevel P).primeFactors=P.image (fun p : Nat.Primes => (p : ℕ)) := by
  classical
  unfold criticalPrimeLevel
  rw [← Finset.prod_image (f := fun n : ℕ => n) (by
    intro p hp q hq he
    exact Subtype.ext he)]
  apply Nat.primeFactors_prod
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  exact q.property

def criticalCofactor (P : Finset Nat.Primes) (s : ℂ) : ℂ :=
  DirichletCharacter.LFunctionTrivChar (criticalPrimeLevel P) s

def criticalCofactorTerm (P : Finset Nat.Primes) (s : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (fun m => if m.Coprime (criticalPrimeLevel P) then 1 else 0) s n

theorem criticalCofactorTerm_eq (P : Finset Nat.Primes) (s : ℂ) (n : ℕ) :
    criticalCofactorTerm P s n =
      if n=0 ∨ ¬n.Coprime (criticalPrimeLevel P) then 0 else (n : ℂ)^(-s) := by
  change (if n=0 then 0 else (if n.Coprime (criticalPrimeLevel P) then (1 : ℂ) else 0)/(n : ℂ)^s)=_
  by_cases hn : n=0
  · rw [if_pos hn,if_pos (Or.inl hn)]
  · rw [if_neg hn]
    by_cases hc : n.Coprime (criticalPrimeLevel P)
    · rw [if_pos hc,if_neg (not_or.mpr ⟨hn,not_not.mpr hc⟩),one_div,Complex.cpow_neg]
    · rw [if_neg hc,if_pos (Or.inr hc),zero_div]

private lemma principal_eq (P : Finset Nat.Primes) (n : ℕ) :
    (1 : DirichletCharacter ℂ (criticalPrimeLevel P)) n=
      if n.Coprime (criticalPrimeLevel P) then 1 else 0 := by
  by_cases hn : n.Coprime (criticalPrimeLevel P)
  · rw [if_pos hn]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime _ _).mpr hn)
  · rw [if_neg hn]
    exact MulChar.map_nonunit _ (fun h => hn ((ZMod.isUnit_iff_coprime _ _).mp h))

theorem criticalCofactor_hasSum (P : Finset Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    HasSum (criticalCofactorTerm P s) (criticalCofactor P s) := by
  have h := (DirichletCharacter.LSeriesSummable_of_one_lt_re
    (1 : DirichletCharacter ℂ (criticalPrimeLevel P)) hs).hasSum
  change HasSum _ (LSeries _ s) at h
  rw [← DirichletCharacter.LFunction_eq_LSeries _ hs] at h
  change HasSum (LSeries.term (fun n => if n.Coprime (criticalPrimeLevel P) then 1 else 0) s)
    ((1 : DirichletCharacter ℂ (criticalPrimeLevel P)).LFunction s)
  convert h using 1
  congr 1
  funext n
  exact (principal_eq P n).symm

theorem criticalCofactor_eq (P : Finset Nat.Primes) {s : ℂ} (hs : s ≠ 1) :
    criticalCofactor P s = (∏ p : P, (1-cubicPrimeBase p s))*riemannZeta s := by
  rw [criticalCofactor,DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs,
    level_primeFactors,Finset.prod_image]
  · congr 1
    exact (Finset.prod_coe_sort P (fun p : Nat.Primes => 1-cubicPrimeBase p s)).symm
  · intro p hp q hq he
    exact Subtype.ext he

theorem criticalCofactor_residue (P : Finset Nat.Primes) :
    Tendsto (fun s => (s-1)*criticalCofactor P s) (𝓝[≠] (1 : ℂ))
      (𝓝 (criticalPrimeNormalization P : ℂ)) := by
  have h := DirichletCharacter.LFunctionTrivChar_residue_one (N := criticalPrimeLevel P)
  have he : (∏ p ∈ (criticalPrimeLevel P).primeFactors, (1-(p : ℂ)⁻¹)) =
      (criticalPrimeNormalization P : ℂ) := by
    rw [level_primeFactors,Finset.prod_image]
    · unfold criticalPrimeNormalization
      push_cast
      simp only [one_div]
      exact (Finset.prod_coe_sort P (fun p : Nat.Primes => 1-(p : ℂ)⁻¹)).symm
    · intro p hp q hq he
      exact Subtype.ext he
  simpa only [criticalCofactor,he] using h

def criticalWeightedLabelEuler (P : Finset Nat.Primes) (p q r : P) (s t : ℂ) : ℂ :=
  ((criticalPrimeNormalization P^3 * criticalPrimeLabelWeight p *
    criticalPrimeLabelWeight q * criticalPrimeLabelWeight r : ℝ) : ℂ) *
    ∏ ℓ : P,
      (cubicPrimeBase ℓ s)^(-criticalLabelShift p ℓ)*
      (cubicPrimeBase ℓ t)^(-criticalLabelShift q ℓ)*
      weightedConeEuler (cubicPrimeBase ℓ 1) (cubicPrimeBase ℓ s) (cubicPrimeBase ℓ t)
        (criticalLabelShift r ℓ-criticalLabelShift p ℓ-criticalLabelShift q ℓ)

def criticalWeightedLabelCone (P : Finset Nat.Primes) (p q r : P) (s t : ℂ)
    (v : P → ℤ × ℤ) : ℂ :=
  ((criticalPrimeNormalization P^3 * criticalPrimeLabelWeight p *
    criticalPrimeLabelWeight q * criticalPrimeLabelWeight r : ℝ) : ℂ) *
    ∏ ℓ : P, weightedShiftedLocal (cubicPrimeBase ℓ 1) (cubicPrimeBase ℓ s)
      (cubicPrimeBase ℓ t) (criticalLabelShift p ℓ) (criticalLabelShift q ℓ)
        (criticalLabelShift r ℓ) (v ℓ)

private lemma weighted_label_hasSum (P : Finset Nat.Primes) (p q r : P)
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    HasSum (criticalWeightedLabelCone P p q r s t) (criticalWeightedLabelEuler P p q r s t) := by
  apply HasSum.mul_left
  apply complex_finite_product_hasSum
  intro ℓ
  have hn (u : ℂ) (hu : 0 < u.re) : ‖cubicPrimeBase ℓ u‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast ℓ.val.property.one_lt) (neg_neg_of_pos hu)
  apply weightedShiftedLocal_hasSum _ (cubicPrimeBase_ne_zero _ _) (cubicPrimeBase_ne_zero _ _)
    (hn s hs) (hn t ht)
  unfold criticalLabelShift
  split_ifs <;> omega

def criticalWeightedConeEuler (P : Finset Nat.Primes) (s t : ℂ) : ℂ :=
  ∑ r : P, ∑ p : P, ∑ q : P,
    if p=r ∨ q=r then 0 else criticalWeightedLabelEuler P p q r s t

def criticalWeightedCone (P : Finset Nat.Primes) (s t : ℂ) (v : P → ℤ × ℤ) : ℂ :=
  ∑ r : P, ∑ p : P, ∑ q : P,
    if p=r ∨ q=r then 0 else criticalWeightedLabelCone P p q r s t v

theorem criticalWeightedCone_hasSum (P : Finset Nat.Primes)
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    HasSum (criticalWeightedCone P s t) (criticalWeightedConeEuler P s t) := by
  apply hasSum_sum
  intro r hr
  apply hasSum_sum
  intro p hp
  apply hasSum_sum
  intro q hq
  by_cases h : p=r ∨ q=r
  · simp only [if_pos h]
    exact hasSum_zero
  · simp only [if_neg h]
    exact weighted_label_hasSum P p q r hs ht

private lemma base_one (p : Nat.Primes) : cubicPrimeBase p 1=(1/(p : ℝ) : ℝ) := by
  simp [cubicPrimeBase,Complex.cpow_neg_one]

private lemma complex_coefficient_real (z : ℝ) (i : ℤ) :
    complexCoefficient (z : ℂ) i=(coefficient z i : ℂ) := by
  unfold complexCoefficient coefficient
  split_ifs <;> push_cast <;> rfl

private lemma weighted_label_balanced (P : Finset Nat.Primes) (p q r : P) (v : P → ℤ × ℤ) :
    criticalWeightedLabelCone P p q r 1 1 v=(criticalLabeledCone P p q r v : ℂ) := by
  unfold criticalWeightedLabelCone criticalLabeledCone
  push_cast
  congr 1
  apply Finset.prod_congr rfl
  intro ℓ hℓ
  simp only [base_one,weightedShiftedLocal,shiftedLocalTriple,complex_coefficient_real]
  push_cast
  rw [zpow_add₀ (one_div_ne_zero (by exact_mod_cast ℓ.val.property.ne_zero))]
  ring

theorem criticalWeightedConeEuler_balanced (P : Finset Nat.Primes) :
    criticalWeightedConeEuler P 1 1 =
      (-criticalPrimeNormalization P * ∑ r : P, criticalThirdLabelWeight r*criticalLabelRow P r^2 : ℝ) := by
  apply (criticalWeightedCone_hasSum P (by norm_num) (by norm_num)).unique
  have h := Complex.hasSum_ofReal.mpr (criticalNoncontractingCone_hasSum P)
  apply h.congr_fun
  intro v
  simp only [criticalWeightedCone,criticalNoncontractingCone,weighted_label_balanced]
  push_cast
  simp only [apply_ite,Complex.ofReal_zero]

private lemma weightedEuler_continuousAt (z : ℂ) (k : ℤ) (hz1 : 1-z ≠ 0) {x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hx1 : 1-x ≠ 0) (hy1 : 1-y ≠ 0) :
    ContinuousAt (fun w : ℂ × ℂ => weightedConeEuler z w.1 w.2 k) (x,y) := by
  have he : ContinuousAt (fun w : ℂ × ℂ => weightedEuler z w.1 w.2) (x,y) := by
    unfold weightedEuler
    fun_prop (disch := first | exact hx | exact hy | exact hx1 | exact hy1 | exact hz1 | exact pow_ne_zero _ hz1 | exact mul_ne_zero hx1 hy1 | exact mul_ne_zero hx hy1 | exact mul_ne_zero hy hx1)
  have hm : ContinuousAt (fun w : ℂ × ℂ => weightedConeEulerMinusOne z w.1 w.2) (x,y) := by
    unfold weightedConeEulerMinusOne
    fun_prop (disch := first | exact hx | exact hy | exact hx1 | exact hy1 | exact hz1 | exact pow_ne_zero _ hz1 | exact mul_ne_zero hx1 hy1 | exact mul_ne_zero hx hy1 | exact mul_ne_zero hy hx1)
  have hm2 : ContinuousAt (fun w : ℂ × ℂ => weightedConeEulerMinusTwo z w.1 w.2) (x,y) := by
    unfold weightedConeEulerMinusTwo
    fun_prop (disch := first | exact hx | exact hy | exact hx1 | exact hy1 | exact hz1 | exact pow_ne_zero _ hz1 | exact mul_ne_zero hx1 hy1 | exact mul_ne_zero hx hy1 | exact mul_ne_zero hy hx1)
  unfold weightedConeEuler
  split_ifs
  · exact hm2
  · exact hm
  · exact he
  · fun_prop (disch := first | exact hx | exact hy | exact hx1 | exact hy1 | exact hz1 | exact pow_ne_zero _ hz1 | exact mul_ne_zero hx1 hy1 | exact mul_ne_zero hx hy1 | exact mul_ne_zero hy hx1)

private lemma base_continuous (p : Nat.Primes) : Continuous (cubicPrimeBase p) := by
  unfold cubicPrimeBase
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  fun_prop

private lemma base_one_sub_ne (p : Nat.Primes) : 1-cubicPrimeBase p 1 ≠ 0 := by
  have h : ‖cubicPrimeBase p 1‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by simp)
  exact sub_ne_zero.mpr (fun he => by rw [← he,norm_one] at h; exact lt_irrefl _ h)

theorem criticalWeightedConeEuler_continuousAt (P : Finset Nat.Primes) :
    ContinuousAt (fun w : ℂ × ℂ => criticalWeightedConeEuler P w.1 w.2) (1,1) := by
  unfold criticalWeightedConeEuler
  apply tendsto_finsetSum
  intro r hr
  apply tendsto_finsetSum
  intro p hp
  apply tendsto_finsetSum
  intro q hq
  by_cases h : p=r ∨ q=r
  · simp only [if_pos h]
    exact continuousAt_const
  · simp only [if_neg h]
    unfold criticalWeightedLabelEuler
    apply ContinuousAt.mul continuousAt_const
    apply tendsto_finsetProd
    intro ℓ hℓ
    have hx : ContinuousAt (fun w : ℂ × ℂ => cubicPrimeBase ℓ w.1) (1,1) :=
      ((base_continuous ℓ).comp continuous_fst).continuousAt
    have hy : ContinuousAt (fun w : ℂ × ℂ => cubicPrimeBase ℓ w.2) (1,1) :=
      ((base_continuous ℓ).comp continuous_snd).continuousAt
    have hc := (weightedEuler_continuousAt (cubicPrimeBase ℓ 1)
      (criticalLabelShift r ℓ-criticalLabelShift p ℓ-criticalLabelShift q ℓ) (base_one_sub_ne ℓ)
      (cubicPrimeBase_ne_zero ℓ 1) (cubicPrimeBase_ne_zero ℓ 1)
      (base_one_sub_ne ℓ) (base_one_sub_ne ℓ)).comp
        (f := fun w : ℂ × ℂ => (cubicPrimeBase ℓ w.1,cubicPrimeBase ℓ w.2)) (hx.prodMk hy)
    exact ((hx.zpow₀ _ (Or.inl (cubicPrimeBase_ne_zero ℓ 1))).mul
      (hy.zpow₀ _ (Or.inl (cubicPrimeBase_ne_zero ℓ 1)))).mul hc

def criticalCompletedCone (P : Finset Nat.Primes) (s t : ℂ)
    (v : (P → ℤ × ℤ) × (ℕ × ℕ)) : ℂ :=
  criticalWeightedCone P s t v.1 *
    (criticalCofactorTerm P s v.2.1 * criticalCofactorTerm P t v.2.2)

def criticalCompletedConeEuler (P : Finset Nat.Primes) (s t : ℂ) : ℂ :=
  criticalWeightedConeEuler P s t * (criticalCofactor P s * criticalCofactor P t)

private lemma completed_mul_hasSum {X Y : Type} {f : X → ℂ} {g : Y → ℂ} {a b : ℂ}
    (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun v : X × Y => f v.1*g v.2) (a*b) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)

theorem criticalCompletedCone_hasSum (P : Finset Nat.Primes) {s t : ℂ}
    (hs : 1 < s.re) (ht : 1 < t.re) :
    HasSum (criticalCompletedCone P s t) (criticalCompletedConeEuler P s t) := by
  have h23 : HasSum
      (fun n : ℕ × ℕ => criticalCofactorTerm P s n.1*criticalCofactorTerm P t n.2)
      (criticalCofactor P s*criticalCofactor P t) :=
    @completed_mul_hasSum ℕ ℕ (criticalCofactorTerm P s) (criticalCofactorTerm P t)
      (criticalCofactor P s) (criticalCofactor P t)
      (criticalCofactor_hasSum P hs) (criticalCofactor_hasSum P ht)
  exact @completed_mul_hasSum (P → ℤ × ℤ) (ℕ × ℕ) (criticalWeightedCone P s t)
    (fun n : ℕ × ℕ => criticalCofactorTerm P s n.1*criticalCofactorTerm P t n.2)
    (criticalWeightedConeEuler P s t) (criticalCofactor P s*criticalCofactor P t)
    (criticalWeightedCone_hasSum P (zero_lt_one.trans hs) (zero_lt_one.trans ht)) h23

/-- The numerator-completed signed source has the exact joint double-pole
coefficient. Both label exclusions and both complex variables are retained. -/
theorem criticalCompletedCone_double_residue (P : Finset Nat.Primes) :
    Tendsto (fun w : ℂ × ℂ => (w.1-1)*(w.2-1)*criticalCompletedConeEuler P w.1 w.2)
      ((𝓝[≠] (1 : ℂ)) ×ˢ (𝓝[≠] (1 : ℂ)))
      (𝓝 ((-criticalPrimeNormalization P^3 *
        ∑ r : P, criticalThirdLabelWeight r*criticalLabelRow P r^2 : ℝ) : ℂ)) := by
  let F := (𝓝[≠] (1 : ℂ)) ×ˢ (𝓝[≠] (1 : ℂ))
  have h0 : Tendsto (id : ℂ → ℂ) (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hx : Tendsto (Prod.fst : ℂ × ℂ → ℂ) F (𝓝 1) := h0.comp tendsto_fst
  have hy : Tendsto (Prod.snd : ℂ × ℂ → ℂ) F (𝓝 1) := h0.comp tendsto_snd
  have hf := (criticalWeightedConeEuler_continuousAt P).tendsto.comp (hx.prodMk_nhds hy)
  have hcx : Tendsto (fun w : ℂ × ℂ => (w.1-1)*criticalCofactor P w.1) F
      (𝓝 (criticalPrimeNormalization P : ℂ)) := (criticalCofactor_residue P).comp tendsto_fst
  have hcy : Tendsto (fun w : ℂ × ℂ => (w.2-1)*criticalCofactor P w.2) F
      (𝓝 (criticalPrimeNormalization P : ℂ)) := (criticalCofactor_residue P).comp tendsto_snd
  have hc := hcx.mul hcy
  have h := hf.mul hc
  rw [criticalWeightedConeEuler_balanced] at h
  convert h using 1
  · funext w
    unfold criticalCompletedConeEuler
    dsimp only [Function.comp_apply]
    ring_nf
  · push_cast
    ring_nf

end RHTower.BAGTrace

