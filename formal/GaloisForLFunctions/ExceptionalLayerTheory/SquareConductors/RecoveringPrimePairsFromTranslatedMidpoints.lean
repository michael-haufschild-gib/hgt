import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheOddFourierModesOfTheSharpPrimeMidpoint

/-!
# Stable recovery of prime support from translated midpoints

El Kaouni's interval Fourier method sees only odd frequencies of the
half-period difference. The possible prime weights, however, are binary
multiples of the known site logarithms. The two opposite sites have
four possible changes, spaced by at least log(4/3) after normalization.
This recovers both halves at every center, including the even centers.
-/
noncomputable section
open Finset Complex
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.MidpointFourier

/-- A binary choice of the logarithmic weight at each site. -/
def selectedLog (P : ℕ → Bool) (m : ℕ) : ℝ := if P m then Real.log m else 0

private def selectedWindow (n : ℕ) (P : ℕ → Bool) (j : ZMod (2*n)) : ℂ :=
  (selectedLog P (2*n+1+j.val):ℝ)

/-- Real translated price of the selected sites in the two opposite half-windows. -/
def midpointReading (n : ℕ) (P : ℕ → Bool) (j : ℕ) : ℝ :=
  (halfDifference (selectedWindow n P) (j:ZMod (2*n))).re

/-- One translated step exposes the difference of the two known endpoint logarithms. -/
theorem logarithmic_midpoint_step {n j : ℕ} (hj : j<n) (P : ℕ → Bool) :
    midpointReading n P (j+1)-midpointReading n P j=
      2*(selectedLog P (2*n+1+j+n)-selectedLog P (2*n+1+j)) := by
  have h := congrArg Complex.re (halfDifference_step (selectedWindow n P) (j:ZMod (2*n)))
  have hv : ((j:ZMod (2*n))+(n:ZMod (2*n))).val=j+n := by
    rw [←Nat.cast_add,ZMod.val_natCast_of_lt (by omega)]
  simpa only [midpointReading,Nat.cast_add,Nat.cast_one,Complex.sub_re,
    selectedWindow,hv,ZMod.val_natCast_of_lt (by omega : j<2*n),
    Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero,
    Complex.ofReal_re,←Nat.add_assoc] using h

private theorem reading_antipode (n : ℕ) (P : ℕ → Bool) :
    midpointReading n P n= -midpointReading n P 0 := by
  have h := congrArg Complex.re (halfDifference_shift (selectedWindow n P) 0)
  simpa only [midpointReading,Nat.cast_zero,zero_add,Complex.neg_re] using h

/-- The least separation between two possible normalized slope values. -/
def logGap := Real.log (4/3:ℝ)
theorem logGap_pos : 0<logGap := Real.log_pos (by norm_num)

private def slopeCode (a b : ℝ) (u v : Bool) := (if v then b else 0)-(if u then a else 0)

private theorem separated_codes {a b : ℝ} (ha : logGap≤a) (hb : logGap≤b-a)
    {u v u' v' : Bool} (h : (u,v)≠(u',v')) :
    logGap≤abs (slopeCode a b u v-slopeCode a b u' v') := by
  have hp := logGap_pos
  cases u <;> cases v <;> cases u' <;> cases v'
  all_goals first
    | exact (h rfl).elim
    | (simp only [slopeCode,Bool.false_eq_true,if_false,if_true];
       first | (apply le_trans _ (le_abs_self _); linarith only [ha,hb,hp])
             | (apply le_trans _ (neg_le_abs _); linarith only [ha,hb,hp]))

private theorem log_separation {n j : ℕ} (hj : j<n) :
    logGap≤Real.log (2*n+1+j:ℕ) ∧
      logGap≤Real.log (2*n+1+j+n:ℕ)-Real.log (2*n+1+j:ℕ) := by
  let m := 2*n+1+j
  have hm0 : 0<(m:ℝ) := Nat.cast_pos.mpr (by dsimp [m];omega)
  have hmax : (m:ℝ)≤3*(n:ℝ) := by exact_mod_cast (show m≤3*n by dsimp [m];omega)
  have hmin : (2:ℝ)≤ m := by exact_mod_cast (show 2≤ m by dsimp [m];omega)
  have hmn : (0:ℝ)<(m+n:ℕ) := by exact_mod_cast (show 0< m+n by dsimp [m];omega)
  change logGap≤Real.log (m:ℝ) ∧ logGap≤Real.log ((m+n:ℕ):ℝ)-Real.log (m:ℝ)
  unfold logGap
  constructor
  · exact Real.log_le_log (by norm_num) (by linarith only [hmin])
  · rw [←Real.log_div hmn.ne' hm0.ne']
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hm0,Nat.cast_add]
    linarith only [hmax]

/-- Equal or sufficiently close translated prices distinguish every pair of
distinct binary logarithm masks on the full interval (2n,4n]. Only the
first n translates are required. -/
theorem identify_binary_log_window (n : ℕ) (P Q : ℕ → Bool)
    (h : ∀ j<n,abs (midpointReading n P j-midpointReading n Q j)<logGap) :
    ∀ m∈Ioc (2*n) (4*n),P m=Q m := by
  have hhalf (j : ℕ) (hj : j<n) :
      (P (2*n+1+j),P (2*n+1+j+n))=(Q (2*n+1+j),Q (2*n+1+j+n)) := by
    have h₀ := abs_lt.mp (h j hj)
    have hNext : abs (midpointReading n P (j+1)-midpointReading n Q (j+1))<logGap := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hj) with hlt|heq
      · exact h _ hlt
      · rw [show j+1 = n from heq,reading_antipode,reading_antipode,neg_sub_neg,abs_sub_comm]
        exact h 0 (by omega)
    have h₁ := abs_lt.mp hNext
    have hs := log_separation hj
    by_contra hh
    have hsep := separated_codes hs.1 hs.2 hh
    change logGap≤abs ((selectedLog P (2*n+1+j+n)-selectedLog P (2*n+1+j))-
      (selectedLog Q (2*n+1+j+n)-selectedLog Q (2*n+1+j))) at hsep
    have hP := logarithmic_midpoint_step hj P
    have hQ := logarithmic_midpoint_step hj Q
    apply (not_lt_of_ge hsep)
    apply abs_lt.mpr
    constructor <;> linarith only [h₀.1,h₀.2,h₁.1,h₁.2,hP,hQ]
  intro m hm
  obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hm
  by_cases hm' : m≤3*n
  · have hh := congrArg Prod.fst (hhalf (m-(2*n+1)) (by omega))
    simpa only [show 2*n+1+(m-(2*n+1))=m by omega] using hh
  · have hh := congrArg Prod.snd (hhalf (m-(3*n+1)) (by omega))
    simpa only [show 2*n+1+(m-(3*n+1))+n=m by omega] using hh

/-- Uniform adversarial readout error below half the logarithmic gap
still determines every selected integer. -/
theorem noisy_binary_log_identification (n : ℕ) (P Q : ℕ → Bool) (Y : ℕ → ℝ)
    (hP : ∀ j<n,abs (Y j-midpointReading n P j)<logGap/2)
    (hQ : ∀ j<n,abs (Y j-midpointReading n Q j)<logGap/2) :
    ∀ m∈Ioc (2*n) (4*n),P m=Q m := by
  apply identify_binary_log_window
  intro j hj
  have hp := abs_lt.mp (hP j hj)
  have hq := abs_lt.mp (hQ j hj)
  exact abs_lt.mpr ⟨by linarith only [hp.2,hq.1],by linarith only [hp.1,hq.2]⟩

private theorem primeReading (n j : ℕ) : midpointReading n (fun m => decide m.Prime) j =
    (halfDifference (primeWindow n) (j:ZMod (2*n))).re := by
  have he : selectedWindow n (fun m => decide m.Prime)=primeWindow n := by
    funext z
    change ((if decide (2*n+1+z.val).Prime then Real.log (2*n+1+z.val:ℕ) else 0:ℝ):ℂ)=
      ((if (2*n+1+z.val).Prime then Real.log (2*n+1+z.val:ℕ) else 0:ℝ):ℂ)
    simp
  simp only [midpointReading,he]

private theorem upper_log_separation {n j : ℕ} (hj : j<n) :
    Real.log 2+logGap≤Real.log (2*n+1+j+n:ℕ) ∧
      Real.log (2*n+1+j+n:ℕ)-Real.log (2*n+1+j:ℕ)≤Real.log 2-logGap := by
  let m := 2*n+1+j
  have hm : (0:ℝ)< m := Nat.cast_pos.mpr (by dsimp [m];omega)
  have hm' : (0:ℝ)<(m+n:ℕ) := Nat.cast_pos.mpr (by dsimp [m];omega)
  have ha : 2*(n:ℝ)≤ m := by exact_mod_cast (show 2*n≤ m by dsimp [m];omega)
  have hb : (3:ℝ)≤(m+n:ℕ) := by exact_mod_cast (show 3≤ m+n by dsimp [m];omega)
  change Real.log 2+logGap≤Real.log (m+n:ℕ) ∧ Real.log (m+n:ℕ)-Real.log (m:ℕ)≤Real.log 2-logGap
  unfold logGap
  constructor
  · rw [←Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_le_log (by norm_num) (by linarith only [hb])
  · rw [←Real.log_div hm'.ne' hm.ne',←Real.log_div (by norm_num) (by norm_num)]
    apply Real.log_le_log (div_pos hm' hm)
    rw [div_le_iff₀ hm,Nat.cast_add]
    linarith only [ha]

private theorem decode_code {a b y : ℝ} {u v : Bool}
    (ha : logGap≤a) (hl : logGap≤b-a) (hb : Real.log 2+logGap≤b)
    (hh : b-a≤Real.log 2-logGap) (hy : abs (y-slopeCode a b u v)<logGap/2) :
    (v=true ↔ logGap/2<y) ∧
      (u=true ↔ y< -(logGap/2) ∨ logGap/2<y ∧ y<Real.log 2) := by
  have hp := logGap_pos
  have ht := Real.log_pos (by norm_num : (1:ℝ)<2)
  have he := abs_lt.mp hy
  cases u <;> cases v <;> simp only [slopeCode,Bool.false_eq_true,if_false,if_true,
    sub_zero,zero_sub] at he
  · have hlow : ¬ y< -(logGap/2) := by linarith only [he.1]
    have hhigh : ¬logGap/2<y := by linarith only [he.2]
    simp [hlow,hhigh]
  · have hhigh : logGap/2<y := by linarith only [hb,ht,hp,he.1]
    have hbig : ¬y<Real.log 2 := by linarith only [hb,hp,he.1]
    have hlow : ¬ y< -(logGap/2) := by linarith only [hhigh,hp]
    simp [hhigh,hbig,hlow]
  · have hlow : y< -(logGap/2) := by linarith only [ha,he.2]
    have hhigh : ¬logGap/2<y := by linarith only [hlow,hp]
    simp [hlow,hhigh]
  · have hhigh : logGap/2<y := by linarith only [hl,he.1]
    have hsmall : y<Real.log 2 := by linarith only [hh,hp,he.2]
    simp [hhigh,hsmall]

/-- Fixed thresholds recover both primality bits from a noisy normalized
price change. A small positive change identifies a prime pair at gap n.
The upper threshold is log 2 for every n. -/
theorem prime_pair_from_noisy_midpoint_step {n j : ℕ} (hj : j<n) (y : ℝ)
    (hy : abs (y-((halfDifference (primeWindow n) ((j+1:ℕ):ZMod (2*n))).re-
      (halfDifference (primeWindow n) (j:ZMod (2*n))).re)/2)<logGap/2) :
    ((2*n+1+j+n).Prime ↔ logGap/2<y) ∧
      ((2*n+1+j).Prime ↔ y< -(logGap/2) ∨ logGap/2<y ∧ y<Real.log 2) := by
  let P := fun m : ℕ => decide m.Prime
  rw [←primeReading,←primeReading,logarithmic_midpoint_step hj,
    mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] at hy
  obtain ⟨h₁,h₂⟩ := log_separation hj
  obtain ⟨h₃,h₄⟩ := upper_log_separation hj
  have he := decode_code (u:=P (2*n+1+j)) (v:=P (2*n+1+j+n)) h₁ h₂ h₃ h₄ hy
  simpa only [P,decide_eq_true_eq] using he

/-- The actual full prime support is determined stably at odd and even
centers by the sharp translated midpoint prices. -/
theorem recover_prime_sites_at_every_center (n : ℕ) (P : ℕ → Bool) (Y : ℕ → ℝ)
    (hactual : ∀ j<n,abs (Y j-(halfDifference (primeWindow n) (j:ZMod (2*n))).re)<logGap/2)
    (hP : ∀ j<n,abs (Y j-midpointReading n P j)<logGap/2) :
    ∀ m∈Ioc (2*n) (4*n),P m=decide m.Prime := by
  exact noisy_binary_log_identification n P _ Y hP (fun j hj => by rw [primeReading]; exact hactual j hj)

private def endpoints (n : ℕ) (m : ℕ) := decide (m=3*n ∨ m=4*n)

private theorem log_ratio_endpoints {n : ℕ} (hn : 0<n) :
    Real.log (4*n:ℕ)-Real.log (3*n:ℕ)=logGap := by
  have hr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  push_cast
  rw [←Real.log_div (by positivity : (4:ℝ)*n≠0) (by positivity : (3:ℝ)*n≠0)]
  unfold logGap
  congr 1
  field_simp

private theorem endpoint_readings {n : ℕ} (hn : 0<n) : ∀ j<n,
    midpointReading n (endpoints n) j= -logGap := by
  let P := endpoints n
  have hey (j : ℕ) (hj : j+1<n) : midpointReading n P (j+1)=midpointReading n P j := by
    have hstep := logarithmic_midpoint_step (show j<n by omega) P
    have hlow : ¬(2*n+1+j=3*n ∨ 2*n+1+j=4*n) := by omega
    have hupp : ¬(2*n+1+j+n=3*n ∨ 2*n+1+j+n=4*n) := by omega
    simp [P,selectedLog,endpoints,hlow,hupp,sub_eq_zero] at hstep
    exact hstep
  have hc (j : ℕ) (hj : j<n) : midpointReading n P j=midpointReading n P 0 := by
    induction j with
    | zero => rfl
    | succ j ih => exact (hey j hj).trans (ih (by omega))
  have hel := logarithmic_midpoint_step (show n-1<n by omega) P
  rw [show n-1+1=n by omega,reading_antipode,hc (n-1) (by omega),
    show 2*n+1+(n-1)=3*n by omega,show 3*n+n=4*n by omega] at hel
  have hlog := log_ratio_endpoints hn
  simp only [P,selectedLog,endpoints,eq_self,or_true,true_or,decide_true,if_true] at hel
  intro j hj
  rw [hc j hj]
  show midpointReading n (endpoints n) 0 = -logGap
  linarith only [hlog,hel]

private theorem empty_readings (n j : ℕ) : midpointReading n (fun _ => false) j=0 := by
  simp [midpointReading,halfDifference,selectedWindow,selectedLog]

/-- Sharpness for the whole observation vector. Selecting the two sites
3n and 4n gives distance exactly log(4/3) from the empty mask at every
one of the n independent translates. Their midpoint fits both masks
with uniform error log(4/3)/2. -/
theorem binary_log_noise_threshold_attained {n : ℕ} (hn : 0<n) :
    ∃ (P Q : ℕ → Bool) (Y : ℕ → ℝ),
      (∃ m∈Ioc (2*n) (4*n),P m≠Q m) ∧
      (∀ j<n,abs (Y j-midpointReading n P j)=logGap/2) ∧
      (∀ j<n,abs (Y j-midpointReading n Q j)=logGap/2) := by
  refine ⟨fun _ => false,endpoints n,fun _ => -logGap/2,?_,?_,?_⟩
  · exact ⟨3*n,mem_Ioc.mpr ⟨by omega,by omega⟩,by simp [endpoints]⟩
  · intro j _
    rw [empty_readings,sub_zero,neg_div,abs_neg,abs_of_nonneg (half_pos logGap_pos).le]
  · intro j hj
    rw [endpoint_readings hn j hj,show -logGap/2- -logGap=logGap/2 by ring,
      abs_of_nonneg (half_pos logGap_pos).le]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval.MidpointFourier
