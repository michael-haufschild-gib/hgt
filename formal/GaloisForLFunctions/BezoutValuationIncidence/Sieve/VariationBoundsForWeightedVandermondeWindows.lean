import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLargeSieveWithTheMontgomeryVaughanConstant
import GaloisForLFunctions.BezoutValuationIncidence.CanonicalPrimitiveSpectralFormAndJordanWindowEnergy

/-!
# Signed variation bounds for sampled Vandermonde energy

The signed layer argument of Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, Proposition 2.4) charges the variation of a spectral
profile. For discrete windows one can center the cumulative discrepancy at
the midpoint of its range. The resulting cost is half the total variation
of the extension by zero, for every signed profile. Intervals attain the
operator comparison. The same estimate applies to primitive divisor modes.
-/

noncomputable section
open Finset RHTower.Sieve GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.HilbertInequality
namespace GaloisForLFunctions.BezoutValuationIncidence.WeightedWindow

/-- Variation of the profile on 0,…,L after extension by zero on both sides. -/
def variation (w : ℕ → ℝ) (L : ℕ) : ℝ :=
  |w 0| + (∑ j ∈ range L, |w j-w (j+1)|) + |w L|

private theorem abel (w V : ℕ → ℝ) (L : ℕ) :
    ∑ j ∈ range (L+1), w j*(V (j+1)-V j) =
      w L*V (L+1)-w 0*V 0 + ∑ j ∈ range L, (w j-w (j+1))*V (j+1) := by
  induction L with
  | zero => simp; ring
  | succ L ih =>
    rw [Finset.sum_range_succ (fun j => w j*(V (j+1)-V j)) (L+1),ih,
      Finset.sum_range_succ (fun j => (w j-w (j+1))*V (j+1)) L]
    ring

/-- An interval discrepancy bound is equivalent, with unchanged constant,
to testing all real profiles with half their total variation. -/
theorem variation_iff_intervals (f : ℕ → ℝ) {H : ℝ} (hH : 0 ≤ H) :
    (∀ A K : ℕ, |∑ j ∈ range K, f (A+j+1)| ≤ H) ↔
    ∀ (A L : ℕ) (w : ℕ → ℝ), |∑ j ∈ range (L+1), w j*f (A+j+1)| ≤ variation w L*(H/2) := by
  constructor
  · intro h A L w
    let P := fun n : ℕ => ∑ j ∈ range n, f (A+j+1)
    have hinc (i k : ℕ) : |P (i+k)-P i| ≤ H := by
      dsimp only [P]
      rw [sum_range_add,add_sub_cancel_left]
      simpa only [← Nat.add_assoc] using h (A+i) k
    have hos (i j : ℕ) : |P j-P i| ≤ H := by
      rcases le_total i j with hij | hji
      · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hij
        exact hinc i k
      · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hji
        rw [abs_sub_comm]
        exact hinc j k
    let S := range (L+2)
    have hne : S.Nonempty := ⟨0,mem_range.mpr (by omega)⟩
    obtain ⟨a,_,ha⟩ := S.exists_min_image P hne
    obtain ⟨b,_,hb⟩ := S.exists_max_image P hne
    let V := fun j => P j-(P a+P b)/2
    have hdiam := (le_abs_self _).trans (hos a b)
    have hV (j : ℕ) (hj : j < L+2) : |V j| ≤ H/2 := by
      have hlow := ha j (mem_range.mpr hj)
      have hhigh := hb j (mem_range.mpr hj)
      rw [abs_le]; dsimp only [V]; constructor <;> linarith only [hdiam,hlow,hhigh]
    have hstep (j : ℕ) : V (j+1)-V j=f (A+j+1) := by
      dsimp only [V,P]
      rw [Finset.sum_range_succ]
      ring
    simp_rw [← hstep]
    rw [abel]
    have hterms : |∑ j ∈ range L, (w j-w (j+1))*V (j+1)| ≤
        (∑ j ∈ range L, |w j-w (j+1)|)*(H/2) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [sum_mul]
      apply sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hV _ (by have := mem_range.mp hj; omega)) (abs_nonneg _)
    have hleft := mul_le_mul_of_nonneg_left (hV 0 (by omega)) (abs_nonneg (w 0))
    have hright := mul_le_mul_of_nonneg_left (hV (L+1) (by omega)) (abs_nonneg (w L))
    refine (abs_add_le _ _).trans ?_
    have he := abs_sub (w L*V (L+1)) (w 0*V 0)
    simp only [abs_mul] at he
    unfold variation
    linarith only [he,hleft,hright,hterms]
  · intro h A K
    cases K with
    | zero => simpa using hH
    | succ L =>
      have ht := h A L (fun _ => 1)
      simpa [variation,show (1+1:ℝ)*(H/2)=H by ring] using ht

private theorem interval_eq {A K : ℕ} (f : ℕ → ℝ) :
    ∑ j ∈ range K, f (A+j+1) = ∑ n ∈ Icc (A+1) (A+K), f n := by
  apply sum_nbij' (fun j => A+j+1) (fun n => n-(A+1))
  · intro j hj; have := mem_range.mp hj; apply mem_Icc.mpr; omega
  · intro n hn; have := mem_Icc.mp hn; apply mem_range.mpr; omega
  · intro j _; omega
  · intro n hn; have := mem_Icc.mp hn; omega
  · intro _ _; rfl

private theorem centered_sum (A K : ℕ) (e : ℕ → ℝ) (E : ℝ) :
    ∑ j ∈ range K, (e (A+j+1)-E) = (∑ n ∈ Icc (A+1) (A+K), e n)-K*E := by
  rw [sum_sub_distrib,interval_eq,sum_const,card_range,nsmul_eq_mul]

/-- Signed sampled energy differs from the signed mass times the column
energy by at most half the zero-extended variation times inverse spacing.
The profile can have arbitrarily many sign changes. -/
theorem weighted_vandermonde {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ r s, r ≠ s → δ ≤ toIntDist (α r-α s))
    (b : ι → ℂ) (A L : ℕ) (w : ℕ → ℝ) :
    let E := ∑ r, ‖b r‖^2
    |∑ j ∈ range (L+1), w j*(‖∑ r, b r*circleFreq (((A+j+1:ℕ):ℝ)*α r)‖^2-E)| ≤
      variation w L*(δ⁻¹*E/2) := by
  intro E
  let e (n : ℕ) := ‖∑ r, b r*circleFreq ((n:ℝ)*α r)‖^2
  have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
  apply (variation_iff_intervals (fun n => e n-E) (mul_nonneg (inv_nonneg.mpr hδ.le) hE)).mp _ A L w
  intro M K
  rw [centered_sum]
  exact abs_sum_window_norm_sq_sub_le α hδ hsep b M K

/-- Vandermonde synthesis at an integer time. -/
def synthesize {ι : Type*} [Fintype ι] (α : ι → ℝ) (b : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ r, b r*circleFreq ((n:ℝ)*α r)

/-- A signed profile with sufficient total mass still gives a positive
lower frame bound. The same interval contains every Rayleigh quotient. -/
theorem signed_frame_bounds {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ r s, r ≠ s → δ ≤ toIntDist (α r-α s))
    (b : ι → ℂ) (A L : ℕ) (w : ℕ → ℝ) :
    let E := ∑ r, ‖b r‖^2
    let mass := ∑ j ∈ range (L+1), w j
    let price := variation w L/(2*δ)
    (∑ j ∈ range (L+1), w j*‖synthesize α b (A+j+1)‖^2) ∈
      Set.Icc ((mass-price)*E) ((mass+price)*E) := by
  intro E mass price
  have h := weighted_vandermonde α hδ hsep b A L w
  simp only [mul_sub,sum_sub_distrib,← sum_mul] at h
  obtain ⟨hl,hu⟩ := abs_le.mp h
  change (_ ≤ _) ∧ (_ ≤ _)
  dsimp only [mass,price,E,synthesize]
  have hp : (2*δ)⁻¹ = δ⁻¹/2 := by ring
  simp only [div_eq_mul_inv,hp] at hl hu ⊢
  constructor <;> linarith only [hl,hu]

/-- Above the variation threshold the difference of any two coefficient
vectors is controlled by the signed energy of the difference of their samples. -/
theorem stable_recovery {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ r s, r ≠ s → δ ≤ toIntDist (α r-α s))
    (b c : ι → ℂ) (A L : ℕ) (w : ℕ → ℝ)
    (hm : variation w L/(2*δ) < ∑ j ∈ range (L+1), w j) :
    ∑ r, ‖b r-c r‖^2 ≤
      (∑ j ∈ range (L+1), w j*‖synthesize α b (A+j+1)-synthesize α c (A+j+1)‖^2) /
        ((∑ j ∈ range (L+1), w j)-variation w L/(2*δ)) := by
  have h := (signed_frame_bounds α hδ hsep (fun r => b r-c r) A L w).1
  have hd (n : ℕ) : synthesize α (fun r => b r-c r) n = synthesize α b n-synthesize α c n := by
    simp only [synthesize,sub_mul,sum_sub_distrib]
  apply (le_div_iff₀ (sub_pos.mpr hm)).mpr
  rw [mul_comm]
  simpa only [hd] using h

private def grid (m : ℕ) (j : Fin m) : ℝ := (j.val:ℝ)/m

private theorem grid_separated {m : ℕ} (hm : 0 < m) {i j : Fin m} (hne : i ≠ j) :
    1/(m:ℝ) ≤ toIntDist (grid m i-grid m j) := by
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  apply one_div_le_toIntDist_of_mul_mem_int hm
  · refine ⟨(i.val:ℤ)-j.val,?_⟩
    dsimp only [grid]; push_cast; field_simp
  · intro n he
    have hg (k : Fin m) : grid m k ∈ Set.Ico 0 1 :=
      ⟨div_nonneg (Nat.cast_nonneg _) hm'.le,(div_lt_one hm').mpr (Nat.cast_lt.mpr k.isLt)⟩
    have hn₁ : (-1:ℤ)<n := by exact_mod_cast (show (-1:ℝ)<n by linarith only [he,(hg i).1,(hg j).2])
    have hn₂ : n < (1:ℤ) := by exact_mod_cast (show (n:ℝ)<1 by linarith only [he,(hg j).1,(hg i).2])
    have hn : n=0 := by omega
    rw [hn,Int.cast_zero,sub_eq_zero] at he
    apply hne
    exact Fin.ext (by exact_mod_cast (div_left_inj' hm'.ne').mp he)

private theorem grid_blind {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    synthesize (grid m) (fun _ => 1) n = 0 := by
  have hm : (0:ℝ) < m := Nat.cast_pos.mpr (hn.trans hnm)
  let z := circleFreq ((n:ℝ)/m)
  have hne : z ≠ 1 := by
    intro he
    obtain ⟨k,hk⟩ := exists_int_of_circleFreq_eq_one he
    have hk₁ : (0:ℤ)<k := by exact_mod_cast (hk ▸ div_pos (Nat.cast_pos.mpr hn) hm)
    have hk₂ : k < (1:ℤ) := by exact_mod_cast (hk ▸ (div_lt_one hm).mpr (Nat.cast_lt.mpr hnm))
    omega
  have hp : z^m=1 := by
    rw [show z=circleFreq ((n:ℝ)/m) from rfl,circleFreq_pow,
      show (m:ℝ)*((n:ℝ)/m)=n by field_simp, circleFreq_natCast]
  have he (j : Fin m) : circleFreq ((n:ℝ)*grid m j)=z^j.val := by
    rw [show z=circleFreq ((n:ℝ)/m) from rfl,circleFreq_pow,grid]; congr 1; ring
  simp only [synthesize,one_mul,he]
  rw [Fin.sum_univ_eq_sum_range (fun j => z^j) m,geom_sum_eq hne,hp,sub_self,zero_div]

/-- No universal improvement in the variation factor is possible. At
m equally spaced nodes the vector of ones is invisible on the first
m−1 samples. The loss of this single sampling class attains the limiting
constant one half. -/
theorem optimal_variation_constant (c : ℝ) :
    (∀ (m : ℕ) (α : Fin m → ℝ) (δ : ℝ), 0 < δ →
      (∀ r s, r ≠ s → δ ≤ toIntDist (α r-α s)) → ∀ (b : Fin m → ℂ) (A L : ℕ) (w : ℕ → ℝ),
      let E := ∑ r, ‖b r‖^2
      |∑ j ∈ range (L+1), w j*(‖synthesize α b (A+j+1)‖^2-E)| ≤ c*variation w L*δ⁻¹*E) ↔
      1/2 ≤ c := by
  constructor
  · intro hall
    by_contra! hsmall
    have hpos : 0 < 1-2*c := by linarith
    obtain ⟨n,hn⟩ := exists_nat_gt (1/(1-2*c))
    let m := n+2
    have hm : 0 < m := by dsimp [m]; omega
    have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
    have he := hall m (grid m) (1/m) (by positivity) (fun _ _ h => grid_separated hm h)
      (fun _ => 1) 0 n (fun _ => 1)
    have energy : (∑ _j : Fin m, ‖(1:ℂ)‖^2) = (m:ℝ) := by simp
    simp only [energy,Nat.zero_add,one_mul,one_div,inv_inv] at he
    have hsum : (∑ j ∈ range (n+1), (‖synthesize (grid m) (fun _ => 1) (j+1)‖^2-(m:ℝ))) =
        ((n:ℝ)+1)*(-(m:ℝ)) := by
      have ht (j : ℕ) (hj : j ∈ range (n+1)) :
          ‖synthesize (grid m) (fun _ => 1) (j+1)‖^2-(m:ℝ) = -(m:ℝ) := by
        have h := mem_range.mp hj
        rw [grid_blind (by omega) (by dsimp [m]; omega)]; simp
      rw [sum_congr rfl ht,sum_const,card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    rw [hsum,abs_mul,abs_neg,abs_of_nonneg hm'.le,abs_of_nonneg (by positivity : 0≤(n:ℝ)+1)] at he
    have hvar : variation (fun _ => 1) n=2 := by simp [variation]; norm_num
    rw [hvar] at he
    have hcancel := (mul_le_mul_iff_left₀ hm').mp he
    change (n:ℝ)+1 ≤ c*2*((n+2:ℕ):ℝ) at hcancel
    push_cast at hcancel
    have hgt := (div_lt_iff₀ hpos).mp hn
    linarith only [hgt,hcancel,hsmall]
  · intro hc m α δ hδ hs b A L w E
    have hv : 0 ≤ variation w L := by unfold variation; positivity
    have hE : 0 ≤ E := sum_nonneg fun _ _ => sq_nonneg _
    refine (weighted_vandermonde α hδ hs b A L w).trans ?_
    change variation w L*(δ⁻¹*E/2) ≤ _
    have h := mul_le_mul_of_nonneg_right hc (mul_nonneg (mul_nonneg hv (inv_nonneg.mpr hδ.le)) hE)
    linarith only [h]

/-- Primitive divisor coordinates retain the sharp Farey spacing on every
signed window. The mean energy is the full Jordan diagonal divided by twelve. -/
theorem weighted_primitive_energy {Q : ℕ} (hQ : 2 ≤ Q) (c : ℕ → ℝ) (A L : ℕ) (w : ℕ → ℝ) :
    let E := sievePrimitiveEnergy Q c
    |∑ j ∈ range (L+1), w j*(weightedCenteredSawtoothSum Q c (A+j+1)^2-E)| ≤
      variation w L*((Q:ℝ)*(Q-1)*E/2) := by
  intro E
  have hE : 0 ≤ E := by unfold E sievePrimitiveEnergy; positivity
  have hQr : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have hC : 0 ≤ (Q:ℝ)*(Q-1)*E := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hE
  apply (variation_iff_intervals (fun n => weightedCenteredSawtoothSum Q c n ^ 2-E) hC).mp _ A L w
  intro M K
  rw [centered_sum M K (fun n => weightedCenteredSawtoothSum Q c n^2) E]
  have he := abs_window_rootsOfUnity_sub_le hQ (T := primitiveRoots' Q)
    (fun z hz => exists_pow_eq_one_of_mem_responseRoots (mem_of_mem_erase hz)) (primitiveSpectralCoeff Q c) M K
  simpa only [← weightedCenteredSawtoothSum_eq_spectral (by omega : 1 ≤ Q),Complex.norm_real,
    Real.norm_eq_abs,sq_abs,sum_norm_sq_primitiveSpectralCoeff (by omega : 1 ≤ Q)] using he

#print axioms variation_iff_intervals
#print axioms weighted_vandermonde
#print axioms signed_frame_bounds
#print axioms stable_recovery
#print axioms optimal_variation_constant
#print axioms weighted_primitive_energy
end GaloisForLFunctions.BezoutValuationIncidence.WeightedWindow
