import GaloisForLFunctions.RHTower.ChiRamanujanMovingLabelRows

/-!
# Uniform control of the complete original labelled source

The original completed cone source is bounded at every frequency by both
zeta factors and its exact four finite Euler factors. The bound retains
both label exclusions, the allowed first/second coincidence, and every
original cofactor. It holds simultaneously at the original growing cutoff.

At a marked prime, use its explicit cofactor-completed numerator instead of
dividing by the unlabelled local factor. Compact annulus bounds therefore
survive its zeros. A summable regular-product majorant, three label indicators,
and Mertens normalization control the full original masked sum.
No source estimate or local unlabelled nonvanishing is assumed.
-/

noncomputable section
open Filter Set Metric
open scoped BigOperators Topology
namespace RHTower.BAGTrace

private def regularMajorant (p : Nat.Primes) : ℝ :=
  cubicMajorant*(p : ℝ)^(-(3/2) : ℝ)

private theorem regularMajorant_nonneg (p : Nat.Primes) : 0 ≤ regularMajorant p := by
  dsimp [regularMajorant,cubicMajorant]
  positivity

private theorem regularMajorant_summable : Summable regularMajorant := by
  have h : Summable (fun p : Nat.Primes => (p : ℝ)^(-(3/2) : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(3/2) : ℝ)< -1)).subtype Nat.Prime
  exact h.mul_left cubicMajorant

private def localF (a b : ℂ) : ℂ := (a+b-a^2-b^2)/(a*b)
private def localG (a b : ℂ) : ℂ := a+b-1-b/a-a/b+b^2/a+a^2/b
private def firstNumerator (z a b : ℂ) : ℂ :=
  ((a+b-1)+z*((a+b)*localF a b-a*b-1)+
    z^2*(a*b-a-b+a^2+b^2))/(a*(1-z)^2)
private def thirdNumerator (z a b : ℂ) : ℂ :=
  (a*b-a-b+z*(2*(a+b)-a*b-1)-z^2*a*b)/(a*b*(1-z)^3)
private def pairNumerator (z a b : ℂ) : ℂ :=
  (a^2+b^2+a*b-a-b+z*(a*b*(2-localF a b-a-b)-(a+b)*localG a b)+
    z^2*a*b*localG a b)/(a*b*(1-z)^2)
private def numerator (k : Fin 4) (z a b : ℂ) : ℂ :=
  if k=0 then firstNumerator z a b else
  if k=1 then firstNumerator z b a else
  if k=2 then thirdNumerator z a b else pairNumerator z a b

private theorem numerator_continuous (k : Fin 4) {z : ℝ} {a b : ℂ}
    (hz : 1-(z : ℂ) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    ContinuousAt (fun w : ℝ × ℂ × ℂ => numerator k w.1 w.2.1 w.2.2) (z,a,b) := by
  fin_cases k <;> simp [numerator,firstNumerator,thirdNumerator,pairNumerator,localF,localG] <;>
    fun_prop (disch := simp [hz,ha,hb])

private def annulus (A : ℝ) : Set ℂ :=
  closedBall 0 (Real.exp |A|) ∩ {z : ℂ | Real.exp (-|A|) ≤ ‖z‖}

private theorem annulus_compact (A : ℝ) : IsCompact (annulus A) :=
  (isCompact_closedBall (0 : ℂ) _).inter_right (isClosed_le continuous_const continuous_norm)

private theorem annulus_ne {A : ℝ} {a : ℂ} (ha : a∈annulus A) : a ≠ 0 := by
  intro h
  have hh : Real.exp (-|A|)  ≤  ‖a‖ := ha.2
  rw [h,norm_zero] at hh
  exact (not_le_of_gt (Real.exp_pos _)) hh

private theorem all_numerator_bound (A : ℝ) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ z ∈ Icc (0 : ℝ) (1/2), ∀ a∈annulus A, ∀ b∈annulus A,
      ∀ k : Fin 4, ‖numerator k z a b‖ ≤ K := by
  let S : Set (ℝ × ℂ × ℂ) := Icc (0 : ℝ) (1/2) ×ˢ (annulus A ×ˢ annulus A)
  have hS : IsCompact S := isCompact_Icc.prod ((annulus_compact A).prod (annulus_compact A))
  have hcont : ContinuousOn (fun w : ℝ × ℂ × ℂ => fun k : Fin 4 => numerator k w.1 w.2.1 w.2.2) S := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_pi.mpr
    intro k
    apply numerator_continuous k _ (annulus_ne hw.2.1) (annulus_ne hw.2.2)
    intro he
    have hh := congrArg Complex.re (sub_eq_zero.mp he)
    simp only [Complex.one_re,Complex.ofReal_re] at hh
    have hh2 := hw.1.2
    linarith
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨|B|+1,by linarith [abs_nonneg B],?_⟩
  intro z hz a ha b hb k
  have h := (norm_le_pi_norm (fun k : Fin 4 => numerator k z a b) k).trans
    (hB (z,a,b) ⟨hz,ha,hb⟩)
  exact h.trans (by linarith [le_abs_self B])

private theorem small_base {p : Nat.Primes} {s : ℂ} (hs : 3/4 ≤ s.re) :
    ‖cubicPrimeBase p s‖ ≤ 3/4 := by
  have h := radialNome_le (c := 1/8) p.2.two_le (by norm_num)
  norm_num [radialNome] at h
  exact (norm_cubicPrimeBase_le hs).trans h

private theorem complement_bounds {w : ℂ} (hw : ‖w‖ ≤ 3/4) :
    1/4 ≤ ‖1-w‖ ∧ ‖1-w‖ ≤ 2 := by
  have hu := norm_sub_le (1 : ℂ) w
  have hl := norm_add_le (1-w) w
  simp only [norm_one,sub_add_cancel] at hu hl
  constructor <;> linarith

private def localRatio (p : Nat.Primes) (α β : ℂ) : ℂ :=
  ((1-cubicPrimeBase p (1+(β-α)))*(1-cubicPrimeBase p (1+(α-β))))/
    ((1-cubicPrimeBase p (1-α))*(1-cubicPrimeBase p (1-β)))

private theorem localRatio_lower (p : Nat.Primes) {α β : ℂ}
    (hα : |α.re| ≤ 1/16) (hβ : |β.re| ≤ 1/16) : 1 ≤ 64*‖localRatio p α β‖ := by
  have ha := abs_le.mp hα
  have hb := abs_le.mp hβ
  have h1 := complement_bounds (small_base (p := p) (s := 1+(β-α)) (by
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re]; linarith))
  have h2 := complement_bounds (small_base (p := p) (s := 1+(α-β)) (by
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re]; linarith))
  have h3 := complement_bounds (small_base (p := p) (s := 1-α) (by
    simp only [Complex.sub_re,Complex.one_re]; linarith))
  have h4 := complement_bounds (small_base (p := p) (s := 1-β) (by
    simp only [Complex.sub_re,Complex.one_re]; linarith))
  have hnum : (1/16 : ℝ) ≤ ‖1-cubicPrimeBase p (1+(β-α))‖*‖1-cubicPrimeBase p (1+(α-β))‖ := by
    nlinarith [mul_le_mul h1.1 h2.1 (by norm_num : (0 : ℝ) ≤ 1/4) (norm_nonneg _)]
  have hden : ‖1-cubicPrimeBase p (1-α)‖*‖1-cubicPrimeBase p (1-β)‖ ≤ 4 := by
    nlinarith [mul_le_mul h3.2 h4.2 (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  have hdpos : 0<‖1-cubicPrimeBase p (1-α)‖*‖1-cubicPrimeBase p (1-β)‖ :=
    mul_pos (by linarith [h3.1]) (by linarith [h4.1])
  rw [localRatio,norm_div,norm_mul,norm_mul,← mul_div_assoc]
  apply (le_div_iff₀ hdpos).mpr
  nlinarith

private theorem prime_base_annulus (A : ℝ) (p : Nat.Primes) {α : ℂ}
    (hα : |α.re*Real.log (p : ℝ)| ≤ |A|) : cubicPrimeBase p α∈annulus A := by
  have hp : (0 : ℝ)<p := by exact_mod_cast p.2.pos
  have hn : ‖cubicPrimeBase p α‖=Real.exp (-α.re*Real.log (p : ℝ)) := by
    rw [norm_cubicPrimeBase,Real.rpow_def_of_pos hp]
    congr 1
    ring
  have ha := abs_le.mp hα
  constructor
  · rw [mem_closedBall,dist_zero_right,hn]
    apply Real.exp_le_exp.mpr
    linarith
  · change Real.exp (-|A|)  ≤  ‖cubicPrimeBase p α‖
    rw [hn]
    apply Real.exp_le_exp.mpr
    linarith

private def localNumerator (k : Fin 4) (z x y : ℂ) : ℂ :=
  if k=0 then x⁻¹*weightedConeEulerMinusOne z x y else
  if k=1 then y⁻¹*weightedConeEulerMinusOne z x y else
  if k=2 then weightedConeEuler z x y 1 else x⁻¹*y⁻¹*weightedConeEulerMinusTwo z x y

private theorem minusOne_swap (z x y : ℂ) (hz : 1-z  ≠  0)
    (hx : x  ≠  0) (hy : y  ≠  0) (hx1 : 1-x  ≠  0) (hy1 : 1-y  ≠  0) :
    weightedConeEulerMinusOne z x y = weightedConeEulerMinusOne z y x := by
  unfold weightedConeEulerMinusOne weightedEuler
  field_simp
  ring

private theorem numerator_eq (k : Fin 4) (z a b : ℂ)
    (hz : z  ≠  0) (ha : a  ≠  0) (hb : b  ≠  0)
    (h1 : 1-z  ≠  0) (hx : 1-z*a  ≠  0) (hy : 1-z*b  ≠  0) :
    numerator k z a b = (1-z*a)*(1-z*b)*localNumerator k z (z*a) (z*b) := by
  fin_cases k
  · simp [numerator,localNumerator]
    have h := weightedFirst_normalized_deformation z a b hz ha hb h1 hx hy
    unfold firstNumerator localF
    convert h.symm using 1 <;> ring
  · simp [numerator,localNumerator]
    have h := weightedFirst_normalized_deformation z b a hz hb ha h1 hy hx
    rw [minusOne_swap z (z*b) (z*a) h1 (mul_ne_zero hz hb) (mul_ne_zero hz ha) hy hx] at h
    unfold firstNumerator localF
    convert h.symm using 1 <;> ring
  · simp [numerator,localNumerator]
    have h := weightedThird_normalized_deformation z a b hz ha hb h1 hx hy
    exact h.symm
  · simp [numerator,localNumerator]
    have h := weightedPair_normalized_deformation z a b hz ha hb h1 hx hy
    dsimp only at h
    unfold pairNumerator localF localG
    convert h.symm using 1
    ring

private theorem base_complement_ne (p : Nat.Primes) {s : ℂ} (hs : 0 < s.re) :
    1-cubicPrimeBase p s  ≠  0 := by
  have h : ‖cubicPrimeBase p s‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (neg_neg_of_pos hs)
  intro he
  rw [← sub_eq_zero.mp he,norm_one] at h
  exact (lt_irrefl _ h)

private theorem moving_local_factor (p : Nat.Primes) {α β : ℂ}
    (hα : |α.re| < 1/16) (hβ : |β.re| < 1/16) :
    (1-cubicPrimeBase p (1+α))*(1-cubicPrimeBase p (1+β))*
      weightedEuler (cubicPrimeBase p 1) (cubicPrimeBase p (1+α))
        (cubicPrimeBase p (1+β)) =
      cubicPrimeFactor p 1 α β *
      ((1-cubicPrimeBase p (1+(β-α)))*(1-cubicPrimeBase p (1+(α-β))))/
      ((1-cubicPrimeBase p (1-α))*(1-cubicPrimeBase p (1-β))) := by
  have ha := abs_lt.mp hα
  have hb := abs_lt.mp hβ
  have hz := base_complement_ne p (s := 1) (by norm_num)
  have hx := base_complement_ne p (s := 1+α) (by simp only [Complex.add_re,Complex.one_re]; linarith)
  have hy := base_complement_ne p (s := 1+β) (by simp only [Complex.add_re,Complex.one_re]; linarith)
  have hxi := base_complement_ne p (s := 1-α) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have hyi := base_complement_ne p (s := 1-β) (by simp only [Complex.sub_re,Complex.one_re]; linarith)
  have huv := base_complement_ne p (s := 1+(α-β)) (by simp only [Complex.add_re,Complex.sub_re,Complex.one_re]; linarith)
  have hvu := base_complement_ne p (s := 1+(β-α)) (by simp only [Complex.add_re,Complex.sub_re,Complex.one_re]; linarith)
  have h := weightedEuler_eq_regularFactor (cubicPrimeBase_ne_zero p α)
    (cubicPrimeBase_ne_zero p β) hz
    (by simpa only [cubicPrimeBase_mul] using hx)
    (by simpa only [cubicPrimeBase_mul] using hy)
    (by simpa only [cubicPrimeBase_div] using hxi)
    (by simpa only [cubicPrimeBase_div] using hyi)
    (by simpa only [cubicPrimeBase_div,cubicPrimeBase_mul] using huv)
    (by simpa only [cubicPrimeBase_div,cubicPrimeBase_mul] using hvu)
  simp only [cubicPrimeBase_div,cubicPrimeBase_mul] at h
  rw [h,cubicPrimeFactor]
  field_simp



private def completedNumerator (k : Fin 4) (p : Nat.Primes) (α β : ℂ) : ℂ :=
  (1-cubicPrimeBase p (1+α))*(1-cubicPrimeBase p (1+β))*
    localNumerator k (cubicPrimeBase p 1) (cubicPrimeBase p (1+α)) (cubicPrimeBase p (1+β))

private theorem exists_marked_bound (A : ℝ) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ p : Nat.Primes, ∀ α β : ℂ, |α.re|<1/16 → |β.re|<1/16 →
      |α.re*Real.log (p : ℝ)| ≤ |A| → |β.re*Real.log (p : ℝ)| ≤ |A| →
      ∀ k : Fin 4, ‖completedNumerator k p α β‖ ≤ K := by
  obtain ⟨K,hK,hbound⟩ := all_numerator_bound A
  refine ⟨K,hK,?_⟩
  intro p α β hα hβ ha hb k
  have hp : (0 : ℝ)<p := by exact_mod_cast p.2.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.2.two_le
  have hz : cubicPrimeBase p 1=((1/(p : ℝ) : ℝ) : ℂ) := by
    simp [cubicPrimeBase,Complex.cpow_neg_one]
  have hzrange : 1/(p : ℝ)∈Icc (0 : ℝ) (1/2) := by
    constructor
    · positivity
    · rw [div_le_iff₀ hp]; linarith
  have hx := base_complement_ne p (s := 1+α) (by
    simp only [Complex.add_re,Complex.one_re]; have := abs_lt.mp hα; linarith)
  have hy := base_complement_ne p (s := 1+β) (by
    simp only [Complex.add_re,Complex.one_re]; have := abs_lt.mp hβ; linarith)
  have h := numerator_eq k (cubicPrimeBase p 1) (cubicPrimeBase p α) (cubicPrimeBase p β)
    (cubicPrimeBase_ne_zero p 1) (cubicPrimeBase_ne_zero p α) (cubicPrimeBase_ne_zero p β)
    (base_complement_ne p (s := 1) (by norm_num))
    (by simpa only [cubicPrimeBase_mul] using hx)
    (by simpa only [cubicPrimeBase_mul] using hy)
  simp only [cubicPrimeBase_mul] at h
  change ‖(1-cubicPrimeBase p (1+α))*(1-cubicPrimeBase p (1+β))*
    localNumerator k (cubicPrimeBase p 1) (cubicPrimeBase p (1+α)) (cubicPrimeBase p (1+β))‖ ≤ K
  rw [← h,hz]
  exact hbound _ hzrange _ (prime_base_annulus A p ha) _ (prime_base_annulus A p hb) k

private def completedLabelFactor (P : Finset Nat.Primes) (p q r ℓ : P) (α β : ℂ) : ℂ :=
  (1-cubicPrimeBase ℓ (1+α))*(1-cubicPrimeBase ℓ (1+β))*
    ((cubicPrimeBase ℓ (1+α))^(-criticalLabelShift p ℓ)*
      (cubicPrimeBase ℓ (1+β))^(-criticalLabelShift q ℓ)*
      weightedConeEuler (cubicPrimeBase ℓ 1) (cubicPrimeBase ℓ (1+α)) (cubicPrimeBase ℓ (1+β))
        (criticalLabelShift r ℓ-criticalLabelShift p ℓ-criticalLabelShift q ℓ))

private theorem label_factor_cases (P : Finset Nat.Primes) (p q r ℓ : P)
    (hpr : p ≠ r) (hqr : q ≠ r) (α β : ℂ) :
    completedLabelFactor P p q r ℓ α β =
      if ℓ=p then (if p=q then completedNumerator 3 ℓ α β else completedNumerator 0 ℓ α β)
      else if ℓ=q then completedNumerator 1 ℓ α β
      else if ℓ=r then completedNumerator 2 ℓ α β
      else (1-cubicPrimeBase ℓ (1+α))*(1-cubicPrimeBase ℓ (1+β))*
        weightedEuler (cubicPrimeBase ℓ 1) (cubicPrimeBase ℓ (1+α)) (cubicPrimeBase ℓ (1+β)) := by
  by_cases hp : ℓ=p
  · subst ℓ
    by_cases hpq : p=q
    · subst q
      simp [completedLabelFactor,completedNumerator,localNumerator,criticalLabelShift,hpr,
        weightedConeEuler]
    · simp [completedLabelFactor,completedNumerator,localNumerator,criticalLabelShift,hpr,hpq,
        weightedConeEuler]
  · by_cases hq : ℓ=q
    · subst ℓ
      simp [completedLabelFactor,completedNumerator,localNumerator,criticalLabelShift,hp,hqr,
        weightedConeEuler]
    · by_cases hr : ℓ=r
      · subst ℓ
        simp [completedLabelFactor,completedNumerator,localNumerator,criticalLabelShift,hp,hq,
          weightedConeEuler]
      · simp [completedLabelFactor,criticalLabelShift,hp,hq,hr,weightedConeEuler]

private def labelWeight (P : Finset Nat.Primes) (K : ℝ) (p q r ℓ : P) : ℝ :=
  (if ℓ=p then K else 1)*(if ℓ=q then K else 1)*(if ℓ=r then K else 1)

private theorem labelWeight_marked (P : Finset Nat.Primes) {K : ℝ} (hK : 1 ≤ K)
    (p q r ℓ : P) (hm : ℓ=p ∨ ℓ=q ∨ ℓ=r) : K ≤ labelWeight P K p q r ℓ := by
  unfold labelWeight
  split_ifs with h1 h2 h3 <;> simp_all <;> nlinarith [sq_nonneg (K-1)]

private theorem label_factor_bound (P : Finset Nat.Primes) (p q r ℓ : P)
    (hpr : p ≠ r) (hqr : q ≠ r) {α β : ℂ} (hα : |α.re|<1/16) (hβ : |β.re|<1/16)
    {K : ℝ} (hK : 1 ≤ K) (hn : ∀ k : Fin 4, ‖completedNumerator k ℓ α β‖ ≤ K) :
    ‖completedLabelFactor P p q r ℓ α β‖ ≤
      ‖localRatio ℓ α β‖*(1+regularMajorant ℓ)*labelWeight P (64*K) p q r ℓ := by
  have hR := localRatio_lower ℓ hα.le hβ.le
  have hb := regularMajorant_nonneg ℓ
  have hK64 : 1 ≤ 64*K := by linarith
  have hmark (hm : ℓ=p ∨ ℓ=q ∨ ℓ=r) : K ≤
      ‖localRatio ℓ α β‖*(1+regularMajorant ℓ)*labelWeight P (64*K) p q r ℓ := by
    have htag := labelWeight_marked P hK64 p q r ℓ hm
    calc K ≤ ‖localRatio ℓ α β‖*(64*K) := by nlinarith
         _ ≤ ‖localRatio ℓ α β‖*(1+regularMajorant ℓ)*(64*K) := by
           nlinarith [mul_nonneg (mul_nonneg (norm_nonneg (localRatio ℓ α β)) hb)
             (show 0 ≤ 64*K by linarith)]
         _ ≤ _ := by gcongr
  rw [label_factor_cases P p q r ℓ hpr hqr α β]
  by_cases hp : ℓ=p
  · rw [if_pos hp]
    split_ifs with hpq
    · exact (hn 3).trans (hmark (Or.inl hp))
    · exact (hn 0).trans (hmark (Or.inl hp))
  · rw [if_neg hp]
    by_cases hq : ℓ=q
    · rw [if_pos hq]
      exact (hn 1).trans (hmark (Or.inr (Or.inl hq)))
    · rw [if_neg hq]
      by_cases hr : ℓ=r
      · rw [if_pos hr]
        exact (hn 2).trans (hmark (Or.inr (Or.inr hr)))
      · rw [if_neg hr,moving_local_factor ℓ hα hβ,mul_div_assoc]
        change ‖cubicPrimeFactor ℓ 1 α β*localRatio ℓ α β‖ ≤ _
        have hf := norm_cubicPrimeFactor_sub_one_le ℓ (σ := 1) (by norm_num) hα.le hβ.le
        have ht := norm_add_le (cubicPrimeFactor ℓ 1 α β-1) (1 : ℂ)
        simp only [sub_add_cancel,norm_one] at ht
        have hf' : ‖cubicPrimeFactor ℓ 1 α β‖ ≤ 1+regularMajorant ℓ := by
          dsimp [regularMajorant]; linarith
        rw [norm_mul,labelWeight,if_neg hp,if_neg hq,if_neg hr]
        simp only [mul_one]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hf' (norm_nonneg (localRatio ℓ α β))

private theorem completed_label_product_bound (P : Finset Nat.Primes) (p q r : P)
    (hpr : p ≠ r) (hqr : q ≠ r) {α β : ℂ} (hα : |α.re|<1/16) (hβ : |β.re|<1/16)
    {K : ℝ} (hK : 1 ≤ K) (hn : ∀ ℓ : P, ∀ k : Fin 4, ‖completedNumerator k ℓ α β‖ ≤ K) :
    ‖∏ ℓ : P,completedLabelFactor P p q r ℓ α β‖ ≤
      ‖∏ ℓ : P,localRatio ℓ α β‖*Real.exp (∑' p,regularMajorant p)*(64*K)^3 := by
  have hb : (∏ ℓ : P,(1+regularMajorant ℓ)) ≤ Real.exp (∑' p,regularMajorant p) := by
    rw [Finset.prod_coe_sort P (fun p : Nat.Primes => 1+regularMajorant p)]
    exact (Real.prod_one_add_le_exp_sum P regularMajorant_nonneg).trans
      (Real.exp_le_exp.mpr (regularMajorant_summable.sum_le_tsum P
        (fun p _ => regularMajorant_nonneg p)))
  calc ‖∏ ℓ : P,completedLabelFactor P p q r ℓ α β‖ ≤
      ∏ ℓ : P,(‖localRatio ℓ α β‖*(1+regularMajorant ℓ)*labelWeight P (64*K) p q r ℓ) := by
        rw [norm_prod]
        apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        intro ℓ hℓ
        exact label_factor_bound P p q r ℓ hpr hqr hα hβ hK (hn ℓ)
       _ = ‖∏ ℓ : P,localRatio ℓ α β‖*(∏ ℓ : P,(1+regularMajorant ℓ))*(64*K)^3 := by
         simp only [labelWeight,Finset.prod_mul_distrib,Fintype.prod_ite_eq',norm_prod]
         ring
       _ ≤ _ := by gcongr

private def eulerComplements (P : Finset Nat.Primes) (α β : ℂ) : ℂ :=
  ∏ ℓ : P,(1-cubicPrimeBase ℓ (1+α))*(1-cubicPrimeBase ℓ (1+β))

private theorem completed_label_eq (P : Finset Nat.Primes) (p q r : P) (α β : ℂ) :
    eulerComplements P α β * criticalWeightedLabelEuler P p q r (1+α) (1+β) =
      ((criticalPrimeNormalization P^3*criticalPrimeLabelWeight p*
        criticalPrimeLabelWeight q*criticalPrimeLabelWeight r : ℝ) : ℂ)*
        ∏ ℓ : P,completedLabelFactor P p q r ℓ α β := by
  unfold eulerComplements criticalWeightedLabelEuler completedLabelFactor
  simp only [Finset.prod_mul_distrib]
  ring

private theorem label_prime_weight_nonneg (p : Nat.Primes) : 0 ≤ criticalPrimeLabelWeight p := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.2.one_lt.le
  exact div_nonneg (Real.log_nonneg hp) (by positivity)

private theorem completed_label_norm_bound (P : Finset Nat.Primes) (p q r : P)
    (hpr : p ≠ r) (hqr : q ≠ r) {α β : ℂ} (hα : |α.re|<1/16) (hβ : |β.re|<1/16)
    {K : ℝ} (hK : 1 ≤ K) (hn : ∀ ℓ : P, ∀ k : Fin 4, ‖completedNumerator k ℓ α β‖ ≤ K) :
    ‖eulerComplements P α β*criticalWeightedLabelEuler P p q r (1+α) (1+β)‖ ≤
      criticalPrimeNormalization P^3*criticalPrimeLabelWeight p*criticalPrimeLabelWeight q*
        criticalPrimeLabelWeight r *
        (‖∏ ℓ : P,localRatio ℓ α β‖*Real.exp (∑' p,regularMajorant p)*(64*K)^3) := by
  rw [completed_label_eq,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hpos : 0 ≤ criticalPrimeNormalization P^3*criticalPrimeLabelWeight p*
      criticalPrimeLabelWeight q*criticalPrimeLabelWeight r := by
    have hM := (criticalPrimeNormalization_pos P).le
    have hp := label_prime_weight_nonneg p
    have hq := label_prime_weight_nonneg q
    have hr := label_prime_weight_nonneg r
    positivity
  rw [abs_of_nonneg hpos]
  exact mul_le_mul_of_nonneg_left
    (completed_label_product_bound P p q r hpr hqr hα hβ hK hn) hpos

private theorem triple_weight_sum {ι : Type*} [Fintype ι] (w : ι → ℝ) (M D : ℝ) :
    (∑ r,∑ p,∑ q,M*w p*w q*w r*D)=M*(∑ p,w p)^3*D := by
  calc (∑ r,∑ p,∑ q,M*w p*w q*w r*D) = ∑ r,∑ p,∑ q,M*D*w r*w p*w q := by
         apply Finset.sum_congr rfl
         intro r hr
         apply Finset.sum_congr rfl
         intro p hp
         apply Finset.sum_congr rfl
         intro q hq
         ring
       _ = _ := by
         simp only [← Finset.mul_sum,← Finset.sum_mul]
         ring

private theorem full_mask_bound (P : Finset Nat.Primes) {α β : ℂ}
    (hα : |α.re|<1/16) (hβ : |β.re|<1/16)
    {K : ℝ} (hK : 1 ≤ K) (hn : ∀ ℓ : P, ∀ k : Fin 4, ‖completedNumerator k ℓ α β‖ ≤ K) :
    ‖eulerComplements P α β*criticalWeightedConeEuler P (1+α) (1+β)‖ ≤
      criticalPrimeNormalization P^3*(∑ p : P,criticalPrimeLabelWeight p)^3 *
        (‖∏ ℓ : P,localRatio ℓ α β‖*Real.exp (∑' p,regularMajorant p)*(64*K)^3) := by
  let D : ℝ := ‖∏ ℓ : P,localRatio ℓ α β‖*Real.exp (∑' p,regularMajorant p)*(64*K)^3
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlocal (p q r : P) :
      ‖eulerComplements P α β*(if p=r ∨ q=r then 0 else
        criticalWeightedLabelEuler P p q r (1+α) (1+β))‖ ≤
        criticalPrimeNormalization P^3*criticalPrimeLabelWeight p*criticalPrimeLabelWeight q*
          criticalPrimeLabelWeight r*D := by
    by_cases hh : p=r ∨ q=r
    · rw [if_pos hh,mul_zero,norm_zero]
      have hM := (criticalPrimeNormalization_pos P).le
      have hp := label_prime_weight_nonneg p
      have hq := label_prime_weight_nonneg q
      have hr := label_prime_weight_nonneg r
      positivity
    · rw [if_neg hh]
      exact completed_label_norm_bound P p q r (not_or.mp hh).1 (not_or.mp hh).2 hα hβ hK hn
  unfold criticalWeightedConeEuler
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  calc (∑ r : P, ‖∑ p : P, ∑ q : P, eulerComplements P α β*
        (if p=r ∨ q=r then 0 else criticalWeightedLabelEuler P p q r (1+α) (1+β))‖) ≤
      ∑ r : P,∑ p : P,∑ q : P,criticalPrimeNormalization P^3*criticalPrimeLabelWeight p*
        criticalPrimeLabelWeight q*criticalPrimeLabelWeight r*D := by
          apply Finset.sum_le_sum
          intro r hr
          apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro p hp
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun q _ => hlocal p q r))
       _ = _ := triple_weight_sum _ _ _

private theorem prime_label_sum (N : ℕ) :
    (∑ p : Sieve.primeSubtypeLE N,criticalPrimeLabelWeight p)=
      ∑ p ∈ Nat.primesLE N,Real.log (p : ℝ)/(p : ℝ) := by
  rw [Finset.sum_coe_sort (Sieve.primeSubtypeLE N) criticalPrimeLabelWeight]
  exact Sieve.sum_primeSubtypeLE N (fun p => Real.log (p : ℝ)/(p : ℝ))

private theorem normalization_weight_bound : ∃ B : ℝ, 0<B ∧ ∀ᶠ N : ℕ in atTop,
    criticalPrimeNormalization (Sieve.primeSubtypeLE N) *
      (∑ p : Sieve.primeSubtypeLE N,criticalPrimeLabelWeight p) ≤ B := by
  let U := Real.exp (-Real.eulerMascheroniConstant)+1
  let V := 1+Real.log 4
  have hU : 0<U := by dsimp [U]; positivity
  have hV : 0<V := by
    dsimp [V]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
    linarith
  refine ⟨U*V,mul_pos hU hV,?_⟩
  have hm := (Complex.continuous_re.tendsto _).comp criticalPrimeNormalization_logScale_tendsto
  simp only [Function.comp_def,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] at hm
  have hme := hm.eventually (gt_mem_nhds (lt_add_one (Real.exp (-Real.eulerMascheroniConstant))))
  filter_upwards [hme,eventually_ge_atTop 3] with N hN hN3
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hL : 1 ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ (N : ℝ) by linarith [Real.exp_one_lt_d9])
    simpa using hh
  have hW := Sieve.mertensFirst_upper (show 1 ≤ N by omega)
  rw [← prime_label_sum] at hW
  have hM := (criticalPrimeNormalization_pos (Sieve.primeSubtypeLE N)).le
  have hWV : (∑ p : Sieve.primeSubtypeLE N,criticalPrimeLabelWeight p) ≤ V*Real.log N := by
    change (∑ p : Sieve.primeSubtypeLE N,criticalPrimeLabelWeight p) ≤
      (1+Real.log 4)*Real.log N
    apply hW.trans
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)]
  calc criticalPrimeNormalization (Sieve.primeSubtypeLE N) *
      (∑ p : Sieve.primeSubtypeLE N,criticalPrimeLabelWeight p) ≤
        criticalPrimeNormalization (Sieve.primeSubtypeLE N)*(V*Real.log N) := by gcongr
       _ = (criticalPrimeNormalization (Sieve.primeSubtypeLE N)*Real.log N)*V := by ring
       _ ≤ U*V := by gcongr

private theorem completed_source_eq (P : Finset Nat.Primes) {α β : ℂ}
    (hα : 1+α ≠ 1) (hβ : 1+β ≠ 1) :
    criticalCompletedConeEuler P (1+α) (1+β)=
      riemannZeta (1+α)*riemannZeta (1+β)*
        (eulerComplements P α β*criticalWeightedConeEuler P (1+α) (1+β)) := by
  rw [criticalCompletedConeEuler,criticalCofactor_eq P hα,criticalCofactor_eq P hβ,
    eulerComplements,Finset.prod_mul_distrib]
  ring

private theorem point_real (ρ t : ℝ) (N : ℕ) :
    (((ρ/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I).re=ρ/Real.log N := by
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,mul_zero,zero_mul,sub_self,add_zero]

private theorem finite_phase_bound {A ρ : ℝ} (hρ : |ρ| ≤ A) {N : ℕ} (hN : 2 ≤ N)
    (t : ℝ) (p : Sieve.primeSubtypeLE N) :
    |(((ρ/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I).re*Real.log (p : ℝ)| ≤ A := by
  have hp : (0 : ℝ)<(p : ℝ) := by exact_mod_cast p.val.2.pos
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast p.val.2.one_lt.le)
  have hpN : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Sieve.mem_primeSubtypeLE.mp p.property)
  have hlog := Real.log_le_log hp hpN
  rw [point_real,abs_mul,abs_div,abs_of_pos hL,abs_of_nonneg hlp]
  calc |ρ|/Real.log N*Real.log (p : ℝ) ≤ |ρ|/Real.log N*Real.log N := by gcongr
       _ = |ρ| := by field_simp
       _ ≤ A := hρ

/-- A uniform bound for the COMPLETE original growing source by its four
finite Euler factors and both zeta factors. All frequencies and every exact
label collision are retained; no unlabelled local nonvanishing is assumed. -/
theorem criticalCompletedConeEuler_uniform_factor_bound (ρ₁ ρ₂ : {r : ℝ // 0<r}) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop, ∀ t₁ t₂ : ℝ,
      let α : ℂ := (((ρ₁ : ℝ)/Real.log N : ℝ) : ℂ)+(t₁ : ℂ)*Complex.I
      let β : ℂ := (((ρ₂ : ℝ)/Real.log N : ℝ) : ℂ)+(t₂ : ℂ)*Complex.I
      ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N) (1+α) (1+β)‖ ≤
        C*‖riemannZeta (1+α)‖*‖riemannZeta (1+β)‖*
          ‖((∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1+(β-α))))*
            (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1+(α-β)))))/
            ((∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1-α)))*
              (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1-β))))‖ := by
  let A : ℝ := |(ρ₁ : ℝ)|+|(ρ₂ : ℝ)|
  obtain ⟨K,hK,hn⟩ := exists_marked_bound A
  obtain ⟨B,hB,hNB⟩ := normalization_weight_bound
  let C : ℝ := B^3*Real.exp (∑' p,regularMajorant p)*(64*K)^3
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  have hsmall (ρ : ℝ) : ∀ᶠ N : ℕ in atTop, |ρ/Real.log N|<1/16 := by
    have h := (tendsto_drift_zero ρ).abs
    simp only [abs_zero] at h
    exact h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/16))
  filter_upwards [hNB,hsmall ρ₁,hsmall ρ₂,eventually_ge_atTop 2] with N hNB hN1 hN2 hN
  intro t₁ t₂
  let α : ℂ := (((ρ₁ : ℝ)/Real.log N : ℝ) : ℂ)+(t₁ : ℂ)*Complex.I
  let β : ℂ := (((ρ₂ : ℝ)/Real.log N : ℝ) : ℂ)+(t₂ : ℂ)*Complex.I
  have hα : |α.re|<1/16 := by simpa only [α,point_real] using hN1
  have hβ : |β.re|<1/16 := by simpa only [β,point_real] using hN2
  have hnum (p : Sieve.primeSubtypeLE N) (k : Fin 4) : ‖completedNumerator k p α β‖ ≤ K := by
    apply hn p α β hα hβ
    · apply finite_phase_bound (N := N) (t := t₁) _ hN
      exact (le_add_of_nonneg_right (abs_nonneg (ρ₂ : ℝ))).trans (le_abs_self A)
    · apply finite_phase_bound (N := N) (t := t₂) _ hN
      exact (le_add_of_nonneg_left (abs_nonneg (ρ₁ : ℝ))).trans (le_abs_self A)
  have hL : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hne (ρ : {r : ℝ // 0<r}) (t : ℝ) :
      1+(((ρ : ℝ)/Real.log N : ℝ) : ℂ)+(t : ℂ)*Complex.I ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,mul_zero,zero_mul,sub_self,add_zero] at hr
    have : 0<(ρ : ℝ)/Real.log N := div_pos ρ.property hL
    linarith
  have hαne : 1+α ≠ 1 := by simpa only [α,add_assoc] using hne ρ₁ t₁
  have hβne : 1+β ≠ 1 := by simpa only [β,add_assoc] using hne ρ₂ t₂
  have hmask := full_mask_bound (Sieve.primeSubtypeLE N) hα hβ hK hnum
  have hW : 0 ≤ ∑ p : Sieve.primeSubtypeLE N,criticalPrimeLabelWeight p :=
    Finset.sum_nonneg (fun p _ => label_prime_weight_nonneg p)
  have hM := (criticalPrimeNormalization_pos (Sieve.primeSubtypeLE N)).le
  have hMW : criticalPrimeNormalization (Sieve.primeSubtypeLE N)^3 *
      (∑ p : Sieve.primeSubtypeLE N,criticalPrimeLabelWeight p)^3 ≤ B^3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (mul_nonneg hM hW) hNB 3
  have hbound : ‖eulerComplements (Sieve.primeSubtypeLE N) α β*
      criticalWeightedConeEuler (Sieve.primeSubtypeLE N) (1+α) (1+β)‖ ≤
      C*‖∏ p : Sieve.primeSubtypeLE N,localRatio p α β‖ := by
    apply hmask.trans
    calc _ ≤ B^3*(‖∏ p : Sieve.primeSubtypeLE N,localRatio p α β‖*
          Real.exp (∑' p,regularMajorant p)*(64*K)^3) := by gcongr
         _ = _ := by dsimp [C]; ring
  have hprod : (∏ p : Sieve.primeSubtypeLE N,localRatio p α β)=
      ((∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1+(β-α))))*
        (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1+(α-β)))))/
      ((∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1-α)))*
        (∏ p : Sieve.primeSubtypeLE N,(1-cubicPrimeBase p (1-β)))) := by
    simp only [localRatio,Finset.prod_div_distrib,Finset.prod_mul_distrib]
  change ‖criticalCompletedConeEuler (Sieve.primeSubtypeLE N) (1+α) (1+β)‖ ≤ _
  rw [← hprod,completed_source_eq _ hαne hβne,norm_mul,norm_mul]
  calc _ ≤ (‖riemannZeta (1+α)‖*‖riemannZeta (1+β)‖)*
      (C*‖∏ p : Sieve.primeSubtypeLE N,localRatio p α β‖) :=
        mul_le_mul_of_nonneg_left hbound
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
       _ = _ := by ring

end RHTower.BAGTrace
