import GaloisForLFunctions.BiScaleUncertainty.CubicSievePhaseRecovery
import GaloisForLFunctions.BiScaleUncertainty.EvenPrimePairMomentCalculus

/-!
# Sharp sixth-order phase recovery for actual two-mode divisor sieves

All affine observations determine the squares of the coordinates at six and
ten. All translated moments through degree five miss their relative sign, and
every odd moment vanishes. A single zero-lag sixth moment recovers the signed
cross product, giving exact reconstruction up to a common sign, including all
zero-coordinate cases.
-/

open scoped BigOperators
open Finset ZMod
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Actual divisor weights with freely chosen coordinates at six and ten. -/
def evenPairReal (a b : ℝ) (d : ℕ) : ℝ :=
  a*parityReal 0 d + b*(parityReal 1 d-parityReal 0 d)

/-- The two-parameter family includes the original parity-lifted obstruction. -/
theorem evenPairReal_one (b : ℝ) : evenPairReal 1 b = parityReal b := by
  funext d
  unfold evenPairReal parityReal
  split_ifs <;> ring

/-- Exact multiples coordinates of the two-parameter real divisor weights. -/
theorem coordinate_evenPairReal (N : ℕ) (a b : ℝ) (q : ℕ) :
    selbergMultiplesCoord (N+10) (evenPairReal a b) q =
      if q = 6 then a else if q = 10 then b else 0 := by
  have hlin : selbergMultiplesCoord (N+10) (evenPairReal a b) q =
      a*selbergMultiplesCoord (N+10) (parityReal 0) q +
      b*(selbergMultiplesCoord (N+10) (parityReal 1) q -
        selbergMultiplesCoord (N+10) (parityReal 0) q) := by
    simp only [selbergMultiplesCoord, evenPairReal, add_div, mul_div_assoc, sub_div,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hlin, coordinate_parityReal, coordinate_parityReal]
  split_ifs <;> ring

private def paritySign (n : ℕ) : ℝ := if 2 ∣ n then 1 else -1

private theorem paritySign_add (n h : ℕ) : paritySign (n+h) = paritySign n * paritySign h := by
  by_cases hn : 2 ∣ n <;> by_cases hh : 2 ∣ h
  · have hs : 2 ∣ n+h := dvd_add hn hh
    simp [paritySign,hn,hh,hs]
  · have hs : ¬ 2 ∣ n+h := by
      simp only [Nat.dvd_iff_mod_eq_zero] at *
      omega
    simp [paritySign,hn,hh,hs]
  · have hs : ¬ 2 ∣ n+h := by
      simp only [Nat.dvd_iff_mod_eq_zero] at *
      omega
    simp [paritySign,hn,hh,hs]
  · have hs : 2 ∣ n+h := by
      simp only [Nat.dvd_iff_mod_eq_zero] at *
      omega
    simp [paritySign,hn,hh,hs]

/-- Literal sieve response as a parity sign times two centered residue rows. -/
theorem sieveSeq_evenPairReal (N : ℕ) (a b : ℝ) (n : ℕ) :
    sieveSeq (N+10) (evenPairReal a b) n =
      (if 2 ∣ n then (1 : ℝ) else -1) *
        (a*residueRow 3 (n : ZMod 3)+b*residueRow 5 (n : ZMod 5)) := by
  have hlin : sieveSeq (N+10) (evenPairReal a b) n =
      a*sieveSeq (N+10) (parityReal 0) n +
      b*(sieveSeq (N+10) (parityReal 1) n-sieveSeq (N+10) (parityReal 0) n) := by
    simp only [sieveSeq, evenPairReal, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hlin,sieveSeq_parityReal,sieveSeq_parityReal]
  simp only [residueRow,ZMod.natCast_eq_zero_iff]
  split_ifs <;> ring

/-- Complete affine data in this sector retain exactly the two squared coefficients. -/
theorem evenPair_affine_eq_iff (N : ℕ) (a b c d : ℝ) :
    (∀ u v, affineMoment (N+10) (evenPairReal a b) u v =
      affineMoment (N+10) (evenPairReal c d) u v) ↔ a^2=c^2 ∧ b^2=d^2 := by
  rw [affineMoment_eq_iff_comparable]
  constructor
  · intro h
    have h6 := h 6 (by simp) 6 (by simp)
    have h10 := h 10 (by simp) 10 (by simp)
    simpa [coordinate_evenPairReal,pow_two] using And.intro h6 h10
  · rintro ⟨ha,hb⟩ q _ t ht
    have htq := Nat.dvd_of_mem_divisors ht
    simp only [coordinate_evenPairReal]
    by_cases hq6 : q = 6
    · subst q
      have ht10 : t ≠ 10 := by intro he; subst t; norm_num at htq
      by_cases ht6 : t = 6
      · simpa [ht6,pow_two] using ha
      · simp [ht6,ht10]
    by_cases hq10 : q = 10
    · subst q
      have ht6 : t ≠ 6 := by intro he; subst t; norm_num at htq
      by_cases ht10 : t = 10
      · simpa [ht10,pow_two] using hb
      · simp [ht6,ht10]
    simp [hq6,hq10]

private theorem sieveSeq_evenPair_antiperiod (N : ℕ) (a b : ℝ) (n : ℕ) :
    sieveSeq (N+10) (evenPairReal a b) (n+15) =
      -sieveSeq (N+10) (evenPairReal a b) n := by
  have h3 : (15 : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff 15 3).mpr (by norm_num)
  have h5 : (15 : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff 15 5).mpr (by norm_num)
  simp only [sieveSeq_evenPairReal]
  change paritySign (n+15) * _ = -(paritySign n * _)
  have hr3 : residueRow 3 ((n+15 : ℕ) : ZMod 3) = residueRow 3 (n : ZMod 3) := by
    simp [Nat.cast_add,h3]
  have hr5 : residueRow 5 ((n+15 : ℕ) : ZMod 5) = residueRow 5 (n : ZMod 5) := by
    simp [Nat.cast_add,h5]
  have h15 : paritySign 15 = -1 := by norm_num [paritySign]
  rw [paritySign_add,hr3,hr5,h15]
  ring

/-- Every odd translated moment vanishes, for arbitrary real coefficients. -/
theorem evenPair_odd_zero (N : ℕ) (a b : ℝ) (m : ℕ) (h : Fin (2*m+1) → ℕ) :
    translatedMoment (N+10) (evenPairReal a b) h = 0 := by
  apply Complex.ofReal_injective
  rw [translatedMoment_complex_eq]
  have ht (n : ZMod (N+10).factorial) :
      residueSignal (N+10) (fun d => (evenPairReal a b d : ℂ)) (n+15) =
        -residueSignal (N+10) (fun d => (evenPairReal a b d : ℂ)) n := by
    have hn : n+15 = ((n.val+15 : ℕ) : ZMod (N+10).factorial) := by simp
    rw [hn,residueSignal_sieveSeq,sieveSeq_evenPair_antiperiod]
    have hz := residueSignal_sieveSeq (N+10) (evenPairReal a b) n.val
    rw [ZMod.natCast_zmod_val] at hz
    simp [hz]
  simpa only [Complex.ofReal_zero] using
    translationMoment_of_antiperiodic _ 15 ht m (fun i => (h i : ZMod (N+10).factorial))

/-- Every even translated moment is a literal CRT product-row average. -/
theorem evenPair_even_crt (N : ℕ) (a b : ℝ) (m : ℕ) (h : Fin (2*m) → ℕ) :
    translatedMoment (N+10) (evenPairReal a b) h =
      (∏ i, (if 2 ∣ h i then (1 : ℝ) else -1)) *
      ((∑ x : ZMod 3, ∑ y : ZMod 5,
        ∏ i, (a*residueRow 3 (x+(h i : ZMod 3))+
          b*residueRow 5 (y+(h i : ZMod 5)))) / 15) := by
  have hsig (n : ℕ) : (∏ i : Fin (2*m), paritySign (n+h i)) = ∏ i, paritySign (h i) := by
    have hs : paritySign n ^ 2 = 1 := by unfold paritySign; split_ifs <;> norm_num
    simp_rw [paritySign_add]
    rw [Finset.prod_mul_distrib]
    simp [pow_mul,hs]
  have hterm (n : ℕ) : (∏ i, sieveSeq (N+10) (evenPairReal a b) (n+h i)) =
      (∏ i, paritySign (h i)) *
      ∏ i, (a*residueRow 3 ((n : ZMod 3)+(h i : ZMod 3))+
        b*residueRow 5 ((n : ZMod 5)+(h i : ZMod 5))) := by
    simp_rw [sieveSeq_evenPairReal]
    change (∏ i, paritySign (n+h i) * _) = _
    rw [Finset.prod_mul_distrib,hsig]
    simp only [Nat.cast_add]
  unfold translatedMoment
  simp_rw [hterm]
  rw [← Finset.mul_sum,mul_div_assoc]
  exact congrArg ((∏ i, paritySign (h i)) * ·)
    (factorial_average_three_five N (fun x y =>
      ∏ i, (a*residueRow 3 (x+(h i : ZMod 3))+
        b*residueRow 5 (y+(h i : ZMod 5)))))

/-- The zero-lag sixth moment retains a signed cubic cross term. -/
theorem evenPair_sixth (N : ℕ) (a b : ℝ) :
    translatedMoment (N+10) (evenPairReal a b) (fun _ : Fin 6 => 0) =
      22*a^6+360*a^4*b^2+480*a^3*b^3+1560*a^2*b^4+820*b^6 := by
  rw [evenPair_even_crt N a b 3]
  simpa using residue_pair_sixth a b

/-- All translated quartic observations miss the relative sign. -/
theorem evenPair_quartic_flip (N : ℕ) (a b : ℝ) (h : Fin 4 → ℕ) :
    translatedMoment (N+10) (evenPairReal a b) h =
      translatedMoment (N+10) (evenPairReal a (-b)) h := by
  rw [evenPair_even_crt N a b 2,evenPair_even_crt N a (-b) 2,
    residue_pair_quartic_flip a b (fun i => (h i : ZMod 3)) (fun i => (h i : ZMod 5))]

/-- Every translated moment of degree at most five misses the relative sign. -/
theorem evenPair_through_five_flip (N : ℕ) (a b : ℝ) (m : ℕ) (hm : m ≤ 5)
    (h : Fin m → ℕ) :
    translatedMoment (N+10) (evenPairReal a b) h =
      translatedMoment (N+10) (evenPairReal a (-b)) h := by
  interval_cases m
  · simp only [translatedMoment,Fin.prod_univ_zero]
  · rw [evenPair_odd_zero N a b 0,evenPair_odd_zero N a (-b) 0]
  · rw [evenPair_even_crt N a b 1,evenPair_even_crt N a (-b) 1,
      residue_pair_quadratic_flip a b (fun i => (h i : ZMod 3)) (fun i => (h i : ZMod 5))]
  · rw [evenPair_odd_zero N a b 1,evenPair_odd_zero N a (-b) 1]
  · exact evenPair_quartic_flip N a b h
  · rw [evenPair_odd_zero N a b 2,evenPair_odd_zero N a (-b) 2]

/-- Exact signed cross term exposed by the sixth moment. -/
theorem evenPair_sixth_flip_difference (N : ℕ) (a b : ℝ) :
    translatedMoment (N+10) (evenPairReal a b) (fun _ : Fin 6 => 0) -
      translatedMoment (N+10) (evenPairReal a (-b)) (fun _ : Fin 6 => 0) = 960*a^3*b^3 := by
  rw [evenPair_sixth,evenPair_sixth]
  ring

/-- Affine data and one sixth moment recover this entire sector up to a common sign. -/
theorem evenPair_recovery_iff (N : ℕ) (a b c d : ℝ) :
    ((∀ u v, affineMoment (N+10) (evenPairReal a b) u v =
        affineMoment (N+10) (evenPairReal c d) u v) ∧
      translatedMoment (N+10) (evenPairReal a b) (fun _ : Fin 6 => 0) =
        translatedMoment (N+10) (evenPairReal c d) (fun _ : Fin 6 => 0)) ↔
      (c=a ∧ d=b) ∨ (c=-a ∧ d=-b) := by
  rw [evenPair_affine_eq_iff,evenPair_sixth,evenPair_sixth]
  constructor
  · rintro ⟨⟨ha,hb⟩,h6⟩
    have hpoly (x y : ℝ) :
        22*x^6+360*x^4*y^2+480*x^3*y^3+1560*x^2*y^4+820*y^6 =
        22*(x^2)^3+360*(x^2)^2*y^2+480*(x*y)^3+1560*x^2*(y^2)^2+820*(y^2)^3 := by ring
    rw [hpoly,hpoly,ha,hb] at h6
    have hcube : (a*b)^3 = (c*d)^3 := by linarith only [h6]
    have hp : a*b = c*d := (show Odd (3 : ℕ) from ⟨1,rfl⟩).pow_injective hcube
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha with hA | hA <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb with hB | hB
    · exact Or.inl ⟨hA.symm,hB.symm⟩
    · have h0 : c*d = 0 := by rw [hA,hB] at hp; nlinarith only [hp]
      rcases mul_eq_zero.mp h0 with hc | hd
      · right; constructor <;> linarith only [hA,hB,hc]
      · left; constructor <;> linarith only [hA,hB,hd]
    · have h0 : c*d = 0 := by rw [hA,hB] at hp; nlinarith only [hp]
      rcases mul_eq_zero.mp h0 with hc | hd
      · left; constructor <;> linarith only [hA,hB,hc]
      · right; constructor <;> linarith only [hA,hB,hd]
    · right; constructor <;> linarith only [hA,hB]
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact ⟨⟨rfl,rfl⟩,rfl⟩
    · constructor
      · constructor <;> ring
      · ring

/-- Degree six is sharp: all affine and lower translated data agree for an explicit pair. -/
theorem exists_same_affine_through_five_distinct_sixth (N : ℕ) :
    ∃ c e : ℕ → ℝ,
      (∀ u v, affineMoment (N+10) c u v = affineMoment (N+10) e u v) ∧
      (∀ (m : ℕ), m ≤ 5 → ∀ h : Fin m → ℕ,
        translatedMoment (N+10) c h = translatedMoment (N+10) e h) ∧
      translatedMoment (N+10) c (fun _ : Fin 6 => 0) -
        translatedMoment (N+10) e (fun _ : Fin 6 => 0) = 960 := by
  refine ⟨evenPairReal 1 1,evenPairReal 1 (-1),?_,?_,?_⟩
  · apply (evenPair_affine_eq_iff N 1 1 1 (-1)).mpr
    norm_num
  · intro m hm h
    exact evenPair_through_five_flip N 1 1 m hm h
  · simpa using evenPair_sixth_flip_difference N 1 1

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
