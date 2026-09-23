import GaloisForLFunctions.RHTower.MobiusDivisorDilationMeanRenewal
import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreHomothety

/-!
# Actual critical clock products under joint prime insertion and cutoff advance

The logarithmic source is the literal processed divisor head divided by its
original cutoff. At complete integer walls it is exactly the critical
Möbius--divisor Abel action. Its finite correlation keeps both signed heads
and the clock measure. Prime insertion is a causal delay of length `log p`
with gain `1/sqrt p`.

The finite renewal law retains the earlier boundary of each copied term.
For the triangular clock weight `1-t/T`, translation also retains the separate
old and new clock factors. Finite reciprocity combines the two mixed terms
without changing their signs or substituting an infinite-clock limit.

The literal squarefree density factor `p/(p+1)` absorbs the copied positive
diagonal exactly. The density-weighted energy change plus its signed mixed
correlation is the negative clock-boundary surplus, hence is nonpositive.
No sign assumption on that correlation is needed for the complete balance.

This does not bound the remaining mixed correlations through exhaustive core
insertion or control the finite-counting discrepancy uniformly in the core.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private def finitePair (P : Finset ℕ) (Y X : ℝ) : ℝ :=
  ∫ x in Ioc (0 : ℝ) X,
    mobiusDivisorContinuousHead P (Y*x)*mobiusDivisorContinuousHead P x/x^(3 : ℕ)

/-- The actual processed head with its original pointwise linear normalization,
written in logarithmic time. -/
def mobiusDivisorCriticalClockHead (P : Finset ℕ) (t : ℝ) : ℝ :=
  mobiusDivisorContinuousHead P (Real.exp t)/Real.exp t

/-- Finite pairing of the two actual linearly normalized heads with clock
measure `dx/x`. Both the lag and the upper boundary are logarithmic times. -/
def mobiusDivisorCriticalClockPairing (P : Finset ℕ) (lag cutoff : ℝ) : ℝ :=
  (∫ x in Ioc (0 : ℝ) (Real.exp cutoff),
    mobiusDivisorContinuousHead P (Real.exp lag*x)*
      mobiusDivisorContinuousHead P x/x^(3 : ℕ))/Real.exp lag

private lemma pair_zero_integrable (P : Finset ℕ) {Y : ℝ} (hY : 0<Y) :
    IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (Y*x)*
      mobiusDivisorContinuousHead P x/x^(3 : ℕ)) (Ioi 0) := by
  apply (integrable_mobiusDivisorDilationMean_kernel P hY).of_forall_sdiff_eq_zero
    measurableSet_Ioi
  intro x hx
  simp [mobiusDivisorContinuousHead_eq_zero P (le_of_not_gt hx.2)]

private lemma pair_scale (P : Finset ℕ) {A B : ℝ} (hB : 0<B) (x : ℝ) :
    mobiusDivisorContinuousHead P (A*x)*mobiusDivisorContinuousHead P (B*x)/x^(3 : ℕ) =
      B^(3 : ℕ)*(mobiusDivisorContinuousHead P ((A/B)*(B*x))*
        mobiusDivisorContinuousHead P (B*x)/(B*x)^(3 : ℕ)) := by
  rw [show A/B*(B*x)=A*x by field_simp]
  by_cases hx : x=0
  · simp [hx]
  · field_simp

private lemma pair_integrable (P : Finset ℕ) {A B : ℝ}
    (hA : 0<A) (hB : 0<B) (X : ℝ) :
    IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^(3 : ℕ)) (Ioc 0 X) := by
  have hi := (integrableOn_Ioi_comp_mul_left_iff _ 0 hB).mpr
    (by simpa using pair_zero_integrable P (div_pos hA hB))
  have hj : IntegrableOn (fun x : ℝ => mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^(3 : ℕ)) (Ioi 0) := by
    apply IntegrableOn.congr_fun (hi.const_mul (B^(3 : ℕ))) _ measurableSet_Ioi
    intro x _
    exact (pair_scale P hB x).symm
  exact hj.mono_set Ioc_subset_Ioi_self

private lemma pair_integral (P : Finset ℕ) {A B X : ℝ}
    (hB : 0<B) (hX : 0≤X) :
    (∫x in Ioc (0:ℝ) X, mobiusDivisorContinuousHead P (A*x)*
      mobiusDivisorContinuousHead P (B*x)/x^(3 : ℕ))=B^(2 : ℕ)*finitePair P (A/B) (B*X) := by
  rw [← intervalIntegral.integral_of_le hX]
  simp_rw [pair_scale P hB]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left
      (fun u : ℝ => mobiusDivisorContinuousHead P ((A/B)*u)*
        mobiusDivisorContinuousHead P u/u^(3 : ℕ)) hB.ne', mul_zero,
    smul_eq_mul, intervalIntegral.integral_of_le (mul_nonneg hB.le hX)]
  unfold finitePair
  field_simp

private lemma finitePair_reciprocal (P : Finset ℕ) {Y X : ℝ}
    (hY : 0<Y) (hX : 0≤X) :
    finitePair P Y X=Y^(2 : ℕ)*finitePair P (1/Y) (Y*X) := by
  have h := pair_integral P (A := 1) hY hX
  calc
    _ = ∫x in Ioc (0:ℝ) X, mobiusDivisorContinuousHead P x*
        mobiusDivisorContinuousHead P (Y*x)/x^(3 : ℕ) := by
      unfold finitePair
      apply integral_congr_ae
      filter_upwards with x
      rw [mul_comm]
    _ = _ := by simpa only [one_mul] using h

private lemma finitePair_joint (P : Finset ℕ) (hP : ∀q∈P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) {Y X : ℝ} (hY : 0<Y) (hX : 0≤X) :
    finitePair (insert p P) Y ((p:ℝ)*X) =
      finitePair P Y ((p:ℝ)*X)+finitePair P Y X/(p:ℝ)-
        Real.sqrt p/(p:ℝ)^(2 : ℕ)*finitePair P ((p:ℝ)*Y) X-
        Real.sqrt p*finitePair P (Y/p) ((p:ℝ)*X) := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  let K : ℝ→ℝ→ℝ→ℝ := fun A B x =>
    mobiusDivisorContinuousHead P (A*x)*mobiusDivisorContinuousHead P (B*x)/x^(3 : ℕ)
  have hi₀ : IntegrableOn (K Y 1) (Ioc 0 ((p:ℝ)*X)) :=
    pair_integrable P hY zero_lt_one _
  have hi₁ : IntegrableOn (K Y (p:ℝ)⁻¹) (Ioc 0 ((p:ℝ)*X)) :=
    pair_integrable P hY (inv_pos.mpr hpR) _
  have hi₂ : IntegrableOn (K (Y/p) 1) (Ioc 0 ((p:ℝ)*X)) :=
    pair_integrable P (div_pos hY hpR) zero_lt_one _
  have hi₃ : IntegrableOn (K (Y/p) (p:ℝ)⁻¹) (Ioc 0 ((p:ℝ)*X)) :=
    pair_integrable P (div_pos hY hpR) (inv_pos.mpr hpR) _
  have he (x : ℝ) :
      mobiusDivisorContinuousHead (insert p P) (Y*x)*
        mobiusDivisorContinuousHead (insert p P) x/x^(3 : ℕ) =
      K Y 1 x-Real.sqrt p*K Y (p:ℝ)⁻¹ x-
        Real.sqrt p*K (Y/p) 1 x+(p:ℝ)*K (Y/p) (p:ℝ)⁻¹ x := by
    simp only [mobiusDivisorContinuousHead_insert P hP hp hpP,K,one_mul]
    rw [show Y*x/(p:ℝ)=(Y/p)*x by ring,show x/(p:ℝ)=(p:ℝ)⁻¹*x by ring]
    have hs := Real.sq_sqrt hpR.le
    linear_combination (mobiusDivisorContinuousHead P (Y/p*x)*
      mobiusDivisorContinuousHead P ((p:ℝ)⁻¹*x)/x^(3 : ℕ))*hs
  unfold finitePair at ⊢
  simp_rw [he]
  change (∫x in Ioc (0:ℝ) ((p:ℝ)*X),
    ((K Y 1-(fun x => Real.sqrt p*K Y (p:ℝ)⁻¹ x))-
      (fun x => Real.sqrt p*K (Y/p) 1 x)) x+
      (fun x => (p:ℝ)*K (Y/p) (p:ℝ)⁻¹ x) x)=_
  rw [integral_add ((hi₀.sub (hi₁.const_mul _)).sub (hi₂.const_mul _)) (hi₃.const_mul _)]
  simp only [Pi.sub_apply]
  have hsub := integral_sub (hi₀.sub (hi₁.const_mul (Real.sqrt p))) (hi₂.const_mul (Real.sqrt p))
  simp only [Pi.sub_apply] at hsub
  rw [hsub,integral_sub hi₀ (hi₁.const_mul _)]
  simp only [integral_const_mul,K]
  rw [pair_integral P zero_lt_one (mul_nonneg hpR.le hX),
    pair_integral P (inv_pos.mpr hpR) (mul_nonneg hpR.le hX),
    pair_integral P zero_lt_one (mul_nonneg hpR.le hX),
    pair_integral P (inv_pos.mpr hpR) (mul_nonneg hpR.le hX)]
  rw [show Y/(p:ℝ)⁻¹=(p:ℝ)*Y by field_simp,
    show (Y/p)/(p:ℝ)⁻¹=Y by field_simp,
    show (p:ℝ)⁻¹*((p:ℝ)*X)=X by field_simp]
  simp only [div_one,one_pow,one_mul]
  unfold finitePair
  field_simp
  ring

/-- The finite pairing retains exactly two original normalized heads and the
clock measure, rather than applying extra decay to either individual head. -/
theorem mobiusDivisorCriticalClockPairing_eq_source_product (P : Finset ℕ) (lag cutoff : ℝ) :
    mobiusDivisorCriticalClockPairing P lag cutoff =
      ∫ x in Ioc (0:ℝ) (Real.exp cutoff),
        (mobiusDivisorContinuousHead P (Real.exp lag*x)/(Real.exp lag*x))*
          (mobiusDivisorContinuousHead P x/x)/x := by
  unfold mobiusDivisorCriticalClockPairing
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x=0
  · simp [hx]
  · field_simp

/-- The arithmetic weighted product is exactly the original two-source
correlation in logarithmic time, with the finite upper clock retained. -/
theorem mobiusDivisorCriticalClockPairing_eq_clock_integral (P : Finset ℕ) (lag cutoff : ℝ) :
    mobiusDivisorCriticalClockPairing P lag cutoff =
      ∫t in Iic cutoff, mobiusDivisorCriticalClockHead P (t+lag)*
        mobiusDivisorCriticalClockHead P t := by
  rw [mobiusDivisorCriticalClockPairing_eq_source_product,← Real.image_exp_Iic]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Iic
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
    Real.exp_injective.injOn]
  apply integral_congr_ae
  filter_upwards with t
  simp only [abs_of_pos (Real.exp_pos t),smul_eq_mul,
    mobiusDivisorCriticalClockHead,Real.exp_add]
  rw [mul_comm (Real.exp t) (Real.exp lag)]
  field_simp

/-- At integer walls the logarithmic source keeps the exact original
processed arithmetic head and its linear cutoff normalization. -/
theorem mobiusDivisorCriticalClockHead_integer_wall (P : Finset Nat.Primes) (M : ℕ) :
    mobiusDivisorCriticalClockHead (P.image (fun p : Nat.Primes => (p:ℕ)))
        (Real.log (M+1:ℕ)) =
      mobiusDivisorSelectionFibre (M+1) (P.image (fun p : Nat.Primes => (p:ℕ))) ∅/(M+1:ℕ) := by
  unfold mobiusDivisorCriticalClockHead
  rw [Real.exp_log (by positivity)]
  rw [mobiusDivisorContinuousHead_nat]
  intro q hq
  obtain ⟨p,_,rfl⟩ := mem_image.mp hq
  exact p.property

private lemma prime_core (P : Finset Nat.Primes) :
    ∀q∈P.image (fun p : Nat.Primes => (p:ℕ)),q.Prime := by
  intro q hq
  obtain ⟨p,_,rfl⟩ := mem_image.mp hq
  exact p.property

private lemma erased_prime_fresh (P : Finset Nat.Primes) (p : Nat.Primes) :
    (p:ℕ)∉(P.erase p).image (fun q : Nat.Primes => (q:ℕ)) := by
  intro h
  obtain ⟨q,hq,he⟩ := mem_image.mp h
  have heq : q=p := Subtype.ext he
  subst q
  exact (notMem_erase p P) hq

private lemma inserted_core (P : Finset Nat.Primes) (p : Nat.Primes) :
    (insert p P).image (fun q : Nat.Primes => (q:ℕ)) =
      insert (p:ℕ) ((P.erase p).image (fun q : Nat.Primes => (q:ℕ))) := by
  have he : insert p (P.erase p)=insert p P := by
    ext q
    by_cases hq : q=p <;> simp [hq]
  rw [← image_insert,he]

private lemma exp_clock (t : ℝ) {p : ℕ} (hp : p.Prime) :
    Real.exp (t+Real.log p)=(p:ℝ)*Real.exp t := by
  rw [Real.exp_add,Real.exp_log (by exact_mod_cast hp.pos),mul_comm]

/-- Every actual prime acts on the critical normalized source as one causal
delay of length `log p`, with the exact gain `1/sqrt p`. -/
theorem mobiusDivisorCriticalClockHead_prime_delay :
    ∀ (P : Finset Nat.Primes) (p : Nat.Primes) (t : ℝ),
      mobiusDivisorCriticalClockHead ((insert p P).image (fun q : Nat.Primes => (q:ℕ))) t =
        mobiusDivisorCriticalClockHead ((P.erase p).image (fun q : Nat.Primes => (q:ℕ))) t-
          mobiusDivisorCriticalClockHead ((P.erase p).image (fun q : Nat.Primes => (q:ℕ)))
            (t-Real.log (p:ℝ))/Real.sqrt (p:ℝ) := by
  intro P p t
  have hpR : (0:ℝ)<(p:ℕ) := by exact_mod_cast p.property.pos
  have hs : Real.sqrt (p:ℕ)≠0 := (Real.sqrt_pos.mpr hpR).ne'
  rw [inserted_core]
  unfold mobiusDivisorCriticalClockHead
  rw [mobiusDivisorContinuousHead_insert _ (prime_core _) p.property (erased_prime_fresh P p),
    Real.exp_sub,Real.exp_log hpR]
  field_simp
  linear_combination -(mobiusDivisorContinuousHead
    ((P.erase p).image (fun q : Nat.Primes => (q:ℕ))) (Real.exp t/(p:ℕ))) *
    (Real.sq_sqrt hpR.le)

private lemma clock_pair_joint (P : Finset ℕ) (hP : ∀q∈P,q.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (lag cutoff : ℝ) :
    mobiusDivisorCriticalClockPairing (insert p P) lag (cutoff+Real.log p) =
      mobiusDivisorCriticalClockPairing P lag (cutoff+Real.log p)+
      mobiusDivisorCriticalClockPairing P lag cutoff/(p:ℝ)-
      (mobiusDivisorCriticalClockPairing P (lag+Real.log p) cutoff+
        mobiusDivisorCriticalClockPairing P (lag-Real.log p) (cutoff+Real.log p))/Real.sqrt p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hs : Real.sqrt p≠0 := (Real.sqrt_pos.mpr hpR).ne'
  have h := finitePair_joint P hP hp hpP (Real.exp_pos lag) (Real.exp_pos cutoff).le
  unfold mobiusDivisorCriticalClockPairing
  change finitePair (insert p P) (Real.exp lag) (Real.exp (cutoff+Real.log p))/Real.exp lag = _
  rw [exp_clock cutoff hp,h]
  rw [exp_clock lag hp,Real.exp_sub,Real.exp_log hpR]
  unfold finitePair
  field_simp
  ring_nf
  simp only [Real.sq_sqrt hpR.le]
  simp only [mul_assoc,mul_left_comm,mul_comm]
  ring

/-- Exact simultaneous core insertion and clock advance. The original signed
product and both distinct finite endpoints survive every term. -/
theorem mobiusDivisorCriticalClockPairing_joint_source_law :
    ∀ (P : Finset Nat.Primes) (p : Nat.Primes) (lag cutoff : ℝ),
      let Q := (P.erase p).image (fun q : Nat.Primes => (q:ℕ))
      mobiusDivisorCriticalClockPairing ((insert p P).image (fun q : Nat.Primes => (q:ℕ)))
          lag (cutoff+Real.log (p:ℝ)) =
        mobiusDivisorCriticalClockPairing Q lag (cutoff+Real.log (p:ℝ))+
        mobiusDivisorCriticalClockPairing Q lag cutoff/(p:ℝ)-
        (mobiusDivisorCriticalClockPairing Q (lag+Real.log (p:ℝ)) cutoff+
          mobiusDivisorCriticalClockPairing Q (lag-Real.log (p:ℝ))
            (cutoff+Real.log (p:ℝ)))/Real.sqrt (p:ℝ) := by
  intro P p lag cutoff
  dsimp only
  rw [inserted_core]
  exact clock_pair_joint _ (prime_core _) p.property (erased_prime_fresh P p) lag cutoff

/-- Finite reciprocity exchanges the two actual heads and transports the
upper clock boundary with their lag. -/
theorem mobiusDivisorCriticalClockPairing_reciprocity (P : Finset ℕ) (lag cutoff : ℝ) :
    mobiusDivisorCriticalClockPairing P lag cutoff =
      mobiusDivisorCriticalClockPairing P (-lag) (cutoff+lag) := by
  have h := finitePair_reciprocal P (Real.exp_pos lag) (Real.exp_pos cutoff).le
  unfold mobiusDivisorCriticalClockPairing
  change finitePair P (Real.exp lag) (Real.exp cutoff)/Real.exp lag = _
  rw [h,Real.exp_neg,Real.exp_add]
  simp only [one_div]
  unfold finitePair
  rw [mul_comm (Real.exp lag) (Real.exp cutoff)]
  field_simp

/-- At zero lag the two mixed terms are the same signed source correlation.
The copied diagonal and its cancelling term retain the earlier cutoff. -/
theorem mobiusDivisorCriticalClockPairing_joint_energy_law :
    ∀ (P : Finset Nat.Primes) (p : Nat.Primes) (cutoff : ℝ),
      let Q := (P.erase p).image (fun q : Nat.Primes => (q:ℕ))
      mobiusDivisorCriticalClockPairing ((insert p P).image (fun q : Nat.Primes => (q:ℕ)))
          0 (cutoff+Real.log (p:ℝ))-
        mobiusDivisorCriticalClockPairing Q 0 (cutoff+Real.log (p:ℝ)) =
        mobiusDivisorCriticalClockPairing Q 0 cutoff/(p:ℝ)-
          2*mobiusDivisorCriticalClockPairing Q (Real.log (p:ℝ)) cutoff/Real.sqrt (p:ℝ) := by
  intro P p cutoff
  have h := mobiusDivisorCriticalClockPairing_joint_source_law P p 0 cutoff
  dsimp only at h ⊢
  simp only [zero_add,zero_sub] at h
  have hr := mobiusDivisorCriticalClockPairing_reciprocity
    ((P.erase p).image (fun q : Nat.Primes => (q:ℕ))) (Real.log (p:ℝ)) cutoff
  rw [← hr] at h
  linear_combination h

private lemma clock_head_zero (P : Finset ℕ) {t : ℝ} (ht : t≤0) :
    mobiusDivisorCriticalClockHead P t=0 := by
  have he : Real.exp t≤1 := by simpa using Real.exp_le_exp.mpr ht
  simp [mobiusDivisorCriticalClockHead,mobiusDivisorContinuousHead_eq_zero P he]

private lemma clock_kernel_integrable (P : Finset ℕ) (lag cutoff : ℝ) :
    IntegrableOn (fun t => mobiusDivisorCriticalClockHead P (t+lag)*
      mobiusDivisorCriticalClockHead P t) (Iic cutoff) := by
  let f : ℝ→ℝ := fun x =>
    (mobiusDivisorContinuousHead P (Real.exp lag*x)*mobiusDivisorContinuousHead P x/x^(3 : ℕ))/
      Real.exp lag
  have hi : IntegrableOn f (Ioc 0 (Real.exp cutoff)) := by
    simpa only [IntegrableOn,f,one_mul] using
      (pair_integrable P (Real.exp_pos lag) zero_lt_one (Real.exp cutoff)).div_const (Real.exp lag)
  have hj := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Iic
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn f).mp
    (by simpa only [Real.image_exp_Iic] using hi)
  apply hj.congr_fun _ measurableSet_Iic
  intro t _
  simp only [f,abs_of_pos (Real.exp_pos t),smul_eq_mul,
    mobiusDivisorCriticalClockHead,Real.exp_add]
  rw [mul_comm (Real.exp t) (Real.exp lag)]
  field_simp

private def agePair (P : Finset ℕ) (lag cutoff : ℝ) : ℝ :=
  ∫t in Iic cutoff, (cutoff-t)*mobiusDivisorCriticalClockHead P (t+lag)*
    mobiusDivisorCriticalClockHead P t

private lemma age_integrable (P : Finset ℕ) (lag cutoff : ℝ) :
    IntegrableOn (fun t => (cutoff-t)*mobiusDivisorCriticalClockHead P (t+lag)*
      mobiusDivisorCriticalClockHead P t) (Iic cutoff) := by
  have hi := (clock_kernel_integrable P lag cutoff).bdd_mul
    (f := fun t : ℝ => cutoff-max 0 t) (c := |cutoff|) (by fun_prop) (by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      change t≤cutoff at ht
      rw [Real.norm_eq_abs]
      by_cases ht0 : t≤0
      · rw [max_eq_left ht0,sub_zero]
      · have htpos : 0≤t := (lt_of_not_ge ht0).le
        rw [max_eq_right htpos,abs_of_nonneg (sub_nonneg.mpr ht),
          abs_of_nonneg (htpos.trans ht)]
        linarith)
  apply IntegrableOn.congr_fun hi _ measurableSet_Iic
  intro t _
  dsimp only
  by_cases ht : t≤0
  · simp [clock_head_zero P ht]
  · rw [max_eq_right (lt_of_not_ge ht).le]
    ring

private lemma shift_image (T B : ℝ) : (fun t : ℝ => t+B) '' Iic T=Iic (T+B) := by
  ext t
  constructor
  · rintro ⟨u,hu,rfl⟩
    change u+B≤T+B
    change u≤T at hu
    linarith
  · intro ht
    refine ⟨t-B,by change t-B≤T; change t≤T+B at ht; linarith,by ring⟩

private lemma shift_integrable (f : ℝ→ℝ) (T B : ℝ)
    (hi : IntegrableOn f (Iic (T+B))) :
    IntegrableOn (fun t => f (t+B)) (Iic T) := by
  have h := (integrableOn_image_iff_integrableOn_abs_deriv_smul
    (f := fun t : ℝ => t+B) (measurableSet_Iic (a := T))
    (fun t _ => ((hasDerivAt_id t).add_const B).hasDerivWithinAt)
    (fun a _ b _ hab => add_right_cancel hab) f).mp
    (by simpa only [shift_image] using hi)
  simpa only [abs_one,one_smul] using h

private lemma shift_integral (f : ℝ→ℝ) (T B : ℝ) :
    (∫t in Iic T, f (t+B))=∫t in Iic (T+B), f t := by
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := fun t : ℝ => t+B) (measurableSet_Iic (a := T))
    (fun t _ => ((hasDerivAt_id t).add_const B).hasDerivWithinAt)
    (fun a _ b _ hab => add_right_cancel hab) f
  simpa only [shift_image,abs_one,one_smul] using h.symm

private lemma age_pair_shift (P : Finset ℕ) (A B T t : ℝ) :
    (T-t)*mobiusDivisorCriticalClockHead P (t+A)*mobiusDivisorCriticalClockHead P (t+B) =
      ((T+B)-(t+B))*mobiusDivisorCriticalClockHead P ((t+B)+(A-B))*
        mobiusDivisorCriticalClockHead P (t+B) := by
  rw [show (T+B)-(t+B)=T-t by ring,show (t+B)+(A-B)=t+A by ring]

private lemma age_pair_integrable (P : Finset ℕ) (A B T : ℝ) :
    IntegrableOn (fun t => (T-t)*mobiusDivisorCriticalClockHead P (t+A)*
      mobiusDivisorCriticalClockHead P (t+B)) (Iic T) := by
  have h := shift_integrable _ T B (age_integrable P (A-B) (T+B))
  apply h.congr_fun _ measurableSet_Iic
  intro t _
  exact (age_pair_shift P A B T t).symm

private lemma age_pair_integral (P : Finset ℕ) (A B T : ℝ) :
    (∫t in Iic T, (T-t)*mobiusDivisorCriticalClockHead P (t+A)*
      mobiusDivisorCriticalClockHead P (t+B))=agePair P (A-B) (T+B) := by
  simp_rw [age_pair_shift P A B T]
  exact shift_integral (fun u => ((T+B)-u)*mobiusDivisorCriticalClockHead P (u+(A-B))*
    mobiusDivisorCriticalClockHead P u) T B

private lemma age_reciprocity (P : Finset ℕ) (lag cutoff : ℝ) :
    agePair P lag cutoff=agePair P (-lag) (cutoff+lag) := by
  have h := age_pair_integral P 0 lag cutoff
  simpa only [agePair,add_zero,zero_sub,mul_assoc,mul_left_comm,mul_comm] using h

private lemma age_joint (P : Finset Nat.Primes) (p : Nat.Primes) (lag cutoff : ℝ) :
    let Q := (P.erase p).image (fun q : Nat.Primes => (q:ℕ))
    agePair ((insert p P).image (fun q : Nat.Primes => (q:ℕ))) lag (cutoff+Real.log (p:ℝ)) =
      agePair Q lag (cutoff+Real.log (p:ℝ))+agePair Q lag cutoff/(p:ℝ)-
        (agePair Q (lag+Real.log (p:ℝ)) cutoff+
          agePair Q (lag-Real.log (p:ℝ)) (cutoff+Real.log (p:ℝ)))/Real.sqrt (p:ℝ) := by
  let Q := (P.erase p).image (fun q : Nat.Primes => (q:ℕ))
  let a : ℝ := Real.log (p:ℝ)
  let r : ℝ := 1/Real.sqrt (p:ℝ)
  let T : ℝ := cutoff+a
  let K : ℝ→ℝ→ℝ→ℝ := fun A B t =>
    (T-t)*mobiusDivisorCriticalClockHead Q (t+A)*mobiusDivisorCriticalClockHead Q (t+B)
  have hpR : (0:ℝ)<(p:ℕ) := by exact_mod_cast p.property.pos
  have hr : r^(2 : ℕ)=1/(p:ℝ) := by
    dsimp [r]
    rw [div_pow,one_pow,Real.sq_sqrt hpR.le]
  have hi₀ : IntegrableOn (K lag 0) (Iic T) := age_pair_integrable Q lag 0 T
  have hi₁ : IntegrableOn (K lag (-a)) (Iic T) := age_pair_integrable Q lag (-a) T
  have hi₂ : IntegrableOn (K (lag-a) 0) (Iic T) := age_pair_integrable Q (lag-a) 0 T
  have hi₃ : IntegrableOn (K (lag-a) (-a)) (Iic T) := age_pair_integrable Q (lag-a) (-a) T
  have he (t : ℝ) :
      (T-t)*mobiusDivisorCriticalClockHead ((insert p P).image (fun q : Nat.Primes => (q:ℕ))) (t+lag)*
        mobiusDivisorCriticalClockHead ((insert p P).image (fun q : Nat.Primes => (q:ℕ))) t =
      K lag 0 t-r*K lag (-a) t-r*K (lag-a) 0 t+(1/(p:ℝ))*K (lag-a) (-a) t := by
    rw [mobiusDivisorCriticalClockHead_prime_delay,mobiusDivisorCriticalClockHead_prime_delay]
    dsimp only [K,Q]
    simp only [add_zero]
    rw [show t+(lag-a)=t+lag-a by ring,show t+ -a=t-a by ring]
    dsimp only [r] at hr ⊢
    linear_combination (T-t)*mobiusDivisorCriticalClockHead Q (t+lag-a)*
      mobiusDivisorCriticalClockHead Q (t-a)*hr
  change agePair _ lag T=agePair Q lag T+agePair Q lag cutoff/(p:ℝ)-
    (agePair Q (lag+a) cutoff+agePair Q (lag-a) T)/Real.sqrt (p:ℝ)
  unfold agePair at ⊢
  simp_rw [he]
  change (∫t in Iic T, ((K lag 0-(fun t => r*K lag (-a) t))-
      (fun t => r*K (lag-a) 0 t)) t+(fun t => (1/(p:ℝ))*K (lag-a) (-a) t) t)=_
  rw [integral_add ((hi₀.sub (hi₁.const_mul _)).sub (hi₂.const_mul _)) (hi₃.const_mul _)]
  simp only [Pi.sub_apply]
  have hs := integral_sub (hi₀.sub (hi₁.const_mul r)) (hi₂.const_mul r)
  simp only [Pi.sub_apply] at hs
  rw [hs,integral_sub hi₀ (hi₁.const_mul r)]
  simp only [integral_const_mul,K]
  rw [age_pair_integral,age_pair_integral,age_pair_integral,age_pair_integral]
  simp only [sub_zero,add_zero,sub_neg_eq_add]
  rw [show lag-a+a=lag by ring,show T+-a=cutoff by dsimp [T]; ring]
  dsimp only [r]
  unfold agePair
  ring

/-- The original triangular clock weight multiplies the complete signed
two-source product. The source vanishes at all nonpositive times. -/
def mobiusDivisorCriticalClockTriangularPairing (P : Finset ℕ) (lag cutoff : ℝ) : ℝ :=
  ∫t in Iic cutoff, (1-t/cutoff)*mobiusDivisorCriticalClockHead P (t+lag)*
    mobiusDivisorCriticalClockHead P t

/-- The literal triangularly weighted product is integrable at every finite
clock and every lag; no source-domain assumption is needed. -/
theorem integrable_mobiusDivisorCriticalClockTriangular_kernel (P : Finset ℕ)
    (lag cutoff : ℝ) :
    IntegrableOn (fun t => (1-t/cutoff)*mobiusDivisorCriticalClockHead P (t+lag)*
      mobiusDivisorCriticalClockHead P t) (Iic cutoff) := by
  by_cases hT : cutoff=0
  · subst cutoff
    apply IntegrableOn.congr_fun integrableOn_zero _ measurableSet_Iic
    intro t ht
    simp [clock_head_zero P ht]
  · have hi := (age_integrable P lag cutoff).div_const cutoff
    apply IntegrableOn.congr_fun hi _ measurableSet_Iic
    intro t _
    dsimp only
    field_simp

private lemma age_eq_clock_mul_triangular (P : Finset ℕ) (lag cutoff : ℝ) :
    agePair P lag cutoff=cutoff*mobiusDivisorCriticalClockTriangularPairing P lag cutoff := by
  unfold agePair mobiusDivisorCriticalClockTriangularPairing
  by_cases hT : cutoff=0
  · subst cutoff
    rw [zero_mul]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    simp [clock_head_zero P ht]
  · rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    field_simp

/-- The finite triangular pairing retains its clock factors under joint
prime insertion and cutoff advance. Neither head nor weight is replaced. -/
theorem mobiusDivisorCriticalClockTriangularPairing_joint_source_law :
    ∀ (P : Finset Nat.Primes) (p : Nat.Primes) (lag cutoff : ℝ),
      let Q := (P.erase p).image (fun q : Nat.Primes => (q:ℕ))
      let a := Real.log (p:ℝ)
      (cutoff+a)*mobiusDivisorCriticalClockTriangularPairing
          ((insert p P).image (fun q : Nat.Primes => (q:ℕ))) lag (cutoff+a) =
        (cutoff+a)*mobiusDivisorCriticalClockTriangularPairing Q lag (cutoff+a)+
        cutoff*mobiusDivisorCriticalClockTriangularPairing Q lag cutoff/(p:ℝ)-
        (cutoff*mobiusDivisorCriticalClockTriangularPairing Q (lag+a) cutoff+
          (cutoff+a)*mobiusDivisorCriticalClockTriangularPairing Q (lag-a) (cutoff+a))/
            Real.sqrt (p:ℝ) := by
  intro P p lag cutoff
  have h := age_joint P p lag cutoff
  dsimp only at h ⊢
  simpa only [age_eq_clock_mul_triangular] using h

/-- At zero lag both triangularly weighted mixed terms combine into one
actual earlier-clock correlation, with the clock normalization retained. -/
theorem mobiusDivisorCriticalClockTriangularPairing_joint_energy_law :
    ∀ (P : Finset Nat.Primes) (p : Nat.Primes) (cutoff : ℝ),
      let Q := (P.erase p).image (fun q : Nat.Primes => (q:ℕ))
      let a := Real.log (p:ℝ)
      (cutoff+a)*(mobiusDivisorCriticalClockTriangularPairing
          ((insert p P).image (fun q : Nat.Primes => (q:ℕ))) 0 (cutoff+a)-
        mobiusDivisorCriticalClockTriangularPairing Q 0 (cutoff+a)) =
        cutoff*mobiusDivisorCriticalClockTriangularPairing Q 0 cutoff/(p:ℝ)-
          2*cutoff*mobiusDivisorCriticalClockTriangularPairing Q a cutoff/Real.sqrt (p:ℝ) := by
  intro P p cutoff
  have h := age_joint P p 0 cutoff
  dsimp only at h ⊢
  simp only [zero_add,zero_sub] at h
  have hr := age_reciprocity ((P.erase p).image (fun q : Nat.Primes => (q:ℕ)))
    (Real.log (p:ℝ)) cutoff
  rw [← hr] at h
  simp only [age_eq_clock_mul_triangular] at h
  linear_combination h

/-- At complete integer walls the clock source is exactly the original
critical Möbius--divisor Abel action, with its original cutoff denominator. -/
theorem mobiusDivisorCriticalClockHead_complete_integer_wall (M : ℕ) :
    mobiusDivisorCriticalClockHead (mobiusDivisorSelectionPrimes (M+1))
      (Real.log (M+1:ℕ))=mobiusDivisorSquareRootAbelMoment (M+1)/(M+1:ℕ) := by
  have hprime : ∀p∈mobiusDivisorSelectionPrimes (M+1),p.Prime := by
    intro p hp
    exact (mem_filter.mp hp).2
  unfold mobiusDivisorCriticalClockHead
  rw [Real.exp_log (by positivity),mobiusDivisorContinuousHead_nat _ hprime,
    mobiusDivisorSelectionFibre_of_all_source_primes_processed (M+1)
      (mobiusDivisorSelectionPrimes (M+1)) ∅ (by rfl),if_pos rfl,
    mobiusDivisorSquareRootAbelMoment_eq_sum_dilationChannels]
  simp only [Nat.add_sub_cancel]
  rw [sum_Icc_succ_top (show 1≤M+1 by omega)]
  have hz : mobiusDivisorDilationChannel (M+1) (M+1)=0 := by
    simp [mobiusDivisorDilationChannel]
  rw [hz,add_zero]

private lemma age_diagonal_mono (P : Finset ℕ) {T U : ℝ} (hTU : T≤U) :
    agePair P 0 T≤agePair P 0 U := by
  have hset : Iic T⊆Iic U := fun _ ht => ht.trans hTU
  have hi := (age_integrable P 0 U).mono_set hset
  calc
    agePair P 0 T ≤ ∫t in Iic T, (U-t)*mobiusDivisorCriticalClockHead P (t+0)*
        mobiusDivisorCriticalClockHead P t := by
      apply integral_mono_ae (age_integrable P 0 T) hi
      filter_upwards with t
      simp only [add_zero]
      have h := mul_nonneg (sub_nonneg.mpr hTU) (sq_nonneg (mobiusDivisorCriticalClockHead P t))
      nlinarith only [h]
    _ ≤ agePair P 0 U := by
      apply setIntegral_mono_set (age_integrable P 0 U)
      · filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
        simp only [add_zero,Pi.zero_apply]
        have h := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg (mobiusDivisorCriticalClockHead P t))
        nlinarith only [h]
      · exact Filter.Eventually.of_forall (fun t ht => hset ht)

/-- The actual squarefree density absorbs the copied diagonal exactly.
The remaining signed mixed product plus density-weighted energy change is
the negative clock-boundary surplus, uniformly in core, prime and cutoff. -/
theorem mobiusDivisorCriticalClockTriangularPairing_density_cancellation :
    ∀ (P : Finset Nat.Primes) (p : Nat.Primes) (cutoff : ℝ),
      let Q := (P.erase p).image (fun q : Nat.Primes => (q:ℕ))
      let R := (insert p P).image (fun q : Nat.Primes => (q:ℕ))
      let ρ := Sieve.squarefreeDensity*∏q∈Q,(q:ℝ)/(q+1)
      let a := Real.log (p:ℝ)
      let balance :=
        (Sieve.squarefreeDensity*∏q∈R,(q:ℝ)/(q+1))*(cutoff+a)*
            mobiusDivisorCriticalClockTriangularPairing R 0 (cutoff+a)-
          ρ*(cutoff+a)*mobiusDivisorCriticalClockTriangularPairing Q 0 (cutoff+a)+
          2*ρ*Real.sqrt (p:ℝ)*cutoff/((p:ℝ)+1)*
            mobiusDivisorCriticalClockTriangularPairing Q a cutoff
      balance = -ρ/((p:ℝ)+1)*
        ((cutoff+a)*mobiusDivisorCriticalClockTriangularPairing Q 0 (cutoff+a)-
          cutoff*mobiusDivisorCriticalClockTriangularPairing Q 0 cutoff) ∧
      balance≤0 := by
  intro P p cutoff
  let Q := (P.erase p).image (fun q : Nat.Primes => (q:ℕ))
  let R := (insert p P).image (fun q : Nat.Primes => (q:ℕ))
  let ρ : ℝ := Sieve.squarefreeDensity*∏q∈Q,(q:ℝ)/(q+1)
  let a : ℝ := Real.log (p:ℝ)
  have hpR : (0:ℝ)<(p:ℕ) := by exact_mod_cast p.property.pos
  have hs : Real.sqrt (p:ℝ)≠0 := (Real.sqrt_pos.mpr hpR).ne'
  have hp1 : (1:ℝ)<(p:ℕ) := by exact_mod_cast p.property.one_lt
  have ha : 0≤a := (Real.log_pos hp1).le
  have hρ : 0≤ρ := by
    dsimp [ρ]
    apply mul_nonneg
    · rw [Sieve.squarefreeDensity_eq]
      positivity
    · apply prod_nonneg
      intro q _
      positivity
  have hρR : (Sieve.squarefreeDensity*∏q∈R,(q:ℝ)/(q+1))=
      ρ*(p:ℝ)/((p:ℝ)+1) := by
    dsimp only [R,Q,ρ]
    rw [inserted_core,prod_insert (erased_prime_fresh P p)]
    ring
  have h := age_joint P p 0 cutoff
  dsimp only at h
  simp only [zero_add,zero_sub] at h
  have hr := age_reciprocity Q a cutoff
  change agePair R 0 (cutoff+a)=agePair Q 0 (cutoff+a)+agePair Q 0 cutoff/(p:ℝ)-
    (agePair Q a cutoff+agePair Q (-a) (cutoff+a))/Real.sqrt (p:ℝ) at h
  rw [← hr] at h
  have hb : (Sieve.squarefreeDensity*∏q∈R,(q:ℝ)/(q+1))*agePair R 0 (cutoff+a)-
      ρ*agePair Q 0 (cutoff+a)+2*ρ*Real.sqrt (p:ℝ)/((p:ℝ)+1)*agePair Q a cutoff =
      -ρ/((p:ℝ)+1)*(agePair Q 0 (cutoff+a)-agePair Q 0 cutoff) := by
    rw [hρR,h]
    field_simp
    ring_nf
    simp only [Real.sq_sqrt hpR.le]
    ring
  have hgap := age_diagonal_mono Q (show cutoff≤cutoff+a by linarith)
  have hn : -ρ/((p:ℝ)+1)*(agePair Q 0 (cutoff+a)-agePair Q 0 cutoff)≤0 :=
    mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hρ)
      (by positivity)) (sub_nonneg.mpr hgap)
  simp only [age_eq_clock_mul_triangular] at hb hn
  dsimp only
  constructor
  · convert hb using 1
    dsimp only [Q,R,ρ,a]
    ring
  · rw [← hb] at hn
    convert hn using 1
    dsimp only [Q,R,ρ,a]
    ring



end RHTower
