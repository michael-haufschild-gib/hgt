import GaloisForLFunctions.BiScaleUncertainty.ParityLiftedSieveMoments
import GaloisForLFunctions.BiScaleUncertainty.AffineSievePhaseRecovery
import Mathlib.Algebra.Order.Ring.Basic

/-!
# Signed odd-mode recovery and the parity obstruction for actual sieve moments

Literal real triple observations recover every signed odd-order multiples
coordinate. Their full data are classified by triangular coordinate products.
Explicit even-mode weights preserve all affine quadratic observations and
annihilate every odd-length translated moment, while their absolute pointwise
amplitudes differ. Thus the joint observation family has no universal decoder
for absolute origin response.
-/

open scoped BigOperators
open Finset ZMod
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Literal complete-period triple average of the existing real divisor response. -/
def tripleMoment (N : ℕ) (c : ℕ → ℝ) (h k : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N.factorial,
    sieveSeq N c n * sieveSeq N c (n+h) * sieveSeq N c (n+k)) / (N.factorial : ℝ)

/-- Literal complete-period average of any finite family of translated real responses. -/
def translatedMoment (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (h : Fin m → ℕ) : ℝ :=
  (∑ n ∈ Finset.range N.factorial, ∏ i, sieveSeq N c (n+h i)) / (N.factorial : ℝ)

/-- The cyclic triple average is exactly the literal real observation. -/
theorem tripleMoment_complex_eq (N : ℕ) (c : ℕ → ℝ) (h k : ℕ) :
    (tripleMoment N c h k : ℂ) =
      tripleCorrelation (residueSignal N (fun d => (c d : ℂ))) h k := by
  unfold tripleMoment tripleCorrelation
  push_cast
  rw [div_eq_mul_inv, mul_comm _ (N.factorial : ℂ)⁻¹]
  apply congrArg ((N.factorial : ℂ)⁻¹ * ·)
  rw [← sum_zmod_val (P := N.factorial)
    (fun n => (sieveSeq N c n : ℂ) * (sieveSeq N c (n+h) : ℂ) * (sieveSeq N c (n+k) : ℂ))]
  apply Finset.sum_congr rfl
  intro n _
  have hh : n+(h : ZMod N.factorial) = ((n.val+h : ℕ) : ZMod N.factorial) := by simp
  have hk : n+(k : ZMod N.factorial) = ((n.val+k : ℕ) : ZMod N.factorial) := by simp
  rw [hh,hk,residueSignal_sieveSeq,residueSignal_sieveSeq]
  have hs := residueSignal_sieveSeq N c n.val
  rw [ZMod.natCast_zmod_val] at hs
  rw [hs]

/-- The cyclic translated product is exactly the literal real complete-period average. -/
theorem translatedMoment_complex_eq (N : ℕ) (c : ℕ → ℝ) {m : ℕ} (h : Fin m → ℕ) :
    (translatedMoment N c h : ℂ) =
      translationMoment (residueSignal N (fun d => (c d : ℂ)))
        (fun i => (h i : ZMod N.factorial)) := by
  unfold translatedMoment translationMoment
  push_cast
  rw [div_eq_mul_inv, mul_comm _ (N.factorial : ℂ)⁻¹]
  apply congrArg ((N.factorial : ℂ)⁻¹ * ·)
  rw [← sum_zmod_val (P := N.factorial)
    (fun n => ∏ i, (sieveSeq N c (n+h i) : ℂ))]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.prod_congr rfl
  intro i _
  have hi : n+(h i : ZMod N.factorial) = ((n.val+h i : ℕ) : ZMod N.factorial) := by simp
  rw [hi,residueSignal_sieveSeq]

/-- The measured double Fourier transform is the exact triangular Selberg-coordinate product. -/
theorem doubleDFT_tripleMoment (N : ℕ) (c : ℕ → ℝ) (r s : ZMod N.factorial) :
    doubleDFT (fun h k : ZMod N.factorial => (tripleMoment N c h.val k.val : ℂ)) r s =
      (N.factorial : ℂ)^2 * (selbergMultiplesCoord N c (addOrderOf r) : ℂ) *
        (selbergMultiplesCoord N c (addOrderOf s) : ℂ) *
        (selbergMultiplesCoord N c (addOrderOf (r+s)) : ℂ) := by
  simpa only [tripleMoment_complex_eq, ZMod.natCast_zmod_val, coordinate_ofReal] using
    doubleDFT_tripleSieve N (fun d => (c d : ℂ)) r s

private theorem tripleMoment_eq_iff_residue (N : ℕ) (c e : ℕ → ℝ) :
    (∀ h k, tripleMoment N c h k = tripleMoment N e h k) ↔
      tripleCorrelation (residueSignal N (fun d => (c d : ℂ))) =
        tripleCorrelation (residueSignal N (fun d => (e d : ℂ))) := by
  constructor
  · intro h
    funext i j
    have he := congrArg (fun x : ℝ => (x : ℂ)) (h i.val j.val)
    simpa only [tripleMoment_complex_eq, ZMod.natCast_zmod_val] using he
  · intro h i j
    apply Complex.ofReal_injective
    rw [tripleMoment_complex_eq,tripleMoment_complex_eq]
    exact congrFun (congrFun h (i : ZMod N.factorial)) (j : ZMod N.factorial)

/-- Complete real triple data retain precisely all triangular coordinate products. -/
theorem tripleMoment_eq_iff_triangles (N : ℕ) (c e : ℕ → ℝ) :
    (∀ h k, tripleMoment N c h k = tripleMoment N e h k) ↔
      ∀ r s : ZMod N.factorial,
        selbergMultiplesCoord N c (addOrderOf r) * selbergMultiplesCoord N c (addOrderOf s) *
          selbergMultiplesCoord N c (addOrderOf (r+s)) =
        selbergMultiplesCoord N e (addOrderOf r) * selbergMultiplesCoord N e (addOrderOf s) *
          selbergMultiplesCoord N e (addOrderOf (r+s)) := by
  rw [tripleMoment_eq_iff_residue,tripleSieve_eq_iff_triangles]
  simp only [coordinate_ofReal, ← Complex.ofReal_mul, Complex.ofReal_inj]

/-- An odd-order coordinate has a literal diagonal cubic Fourier readout. -/
theorem tripleMoment_odd_mode_readout (N : ℕ) (c : ℕ → ℝ) {q : ℕ}
    (hq : q ∈ Finset.Icc 1 N) (hodd : Odd q) :
    doubleDFT (fun h k : ZMod N.factorial => (tripleMoment N c h.val k.val : ℂ))
      ((N.factorial/q : ℕ) : ZMod N.factorial) ((N.factorial/q : ℕ) : ZMod N.factorial) =
        (N.factorial : ℂ)^2 * (selbergMultiplesCoord N c q : ℂ)^3 := by
  simpa only [tripleMoment_complex_eq, ZMod.natCast_zmod_val, coordinate_ofReal] using
    odd_order_diagonal N (fun d => (c d : ℂ)) hq hodd

/-- Full triple observations determine every signed odd-order Selberg coordinate. -/
theorem tripleMoment_recovers_odd_coordinates (N : ℕ) (c e : ℕ → ℝ) :
    (∀ h k, tripleMoment N c h k = tripleMoment N e h k) →
      ∀ q ∈ Finset.Icc 1 N, Odd q → selbergMultiplesCoord N c q = selbergMultiplesCoord N e q := by
  intro h q hq hodd
  have hf : (fun i j : ZMod N.factorial => (tripleMoment N c i.val j.val : ℂ)) =
      (fun i j : ZMod N.factorial => (tripleMoment N e i.val j.val : ℂ)) := by
    funext i j
    rw [h]
  have he := congrFun (congrFun (congrArg doubleDFT hf)
    ((N.factorial/q : ℕ) : ZMod N.factorial)) ((N.factorial/q : ℕ) : ZMod N.factorial)
  rw [tripleMoment_odd_mode_readout N c hq hodd,
    tripleMoment_odd_mode_readout N e hq hodd] at he
  have hP : (N.factorial : ℂ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero N)
  have hc := mul_left_cancel₀ hP he
  have hr : selbergMultiplesCoord N c q ^ 3 = selbergMultiplesCoord N e q ^ 3 := by
    exact_mod_cast hc
  exact (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow_injective hr

/-- Explicit real weights realizing the parity-lifted pair of even modes. -/
def parityReal (t : ℝ) (d : ℕ) : ℝ :=
  (if d = 1 then 1+t else 0) + (if d = 2 then -2*(1+t) else 0) +
    (if d = 3 then -3 else 0) + (if d = 5 then -5*t else 0) +
    (if d = 6 then 6 else 0) + (if d = 10 then 10*t else 0)

/-- The explicit real weight agrees with its complex finite-period realization. -/
theorem parityReal_cast (t : ℝ) (d : ℕ) :
    (parityReal t d : ℂ) = parityWeight (t : ℂ) d := by
  change (parityReal t d : ℂ) =
    (if d = 1 then (1 : ℂ)+(t : ℂ) else 0) +
      (if d = 2 then (-2 : ℂ)*(1+(t : ℂ)) else 0) +
      (if d = 3 then (-3 : ℂ) else 0) + (if d = 5 then (-5 : ℂ)*(t : ℂ) else 0) +
      (if d = 6 then (6 : ℂ) else 0) + (if d = 10 then (10 : ℂ)*(t : ℂ) else 0)
  unfold parityReal
  split_ifs <;> push_cast <;> ring

/-- Exact Selberg coordinates of the concrete real parity family. -/
theorem coordinate_parityReal (N : ℕ) (t : ℝ) (q : ℕ) :
    selbergMultiplesCoord (N+10) (parityReal t) q =
      if q = 6 then 1 else if q = 10 then t else 0 := by
  apply Complex.ofReal_injective
  rw [← coordinate_ofReal]
  simp_rw [parityReal_cast]
  rw [coordinate_parityWeight]
  split_ifs <;> simp

/-- The actual real sieve response factors into a parity sign and an odd-prime pair. -/
theorem sieveSeq_parityReal (N : ℕ) (t : ℝ) (k : ℕ) :
    sieveSeq (N+10) (parityReal t) k =
      (if 2 ∣ k then (1 : ℝ) else -1) *
        (-(1+t) + (if 3 ∣ k then 3 else 0) + (if 5 ∣ k then 5*t else 0)) := by
  apply Complex.ofReal_injective
  rw [← residueSignal_sieveSeq]
  simp_rw [parityReal_cast]
  rw [residueSignal_parityWeight]
  split_ifs <;> push_cast <;> ring

/-- All affine quadratic observations agree for the two real parity weights. -/
theorem parityReal_affineMoment_eq (N a b : ℕ) :
    affineMoment (N+10) (parityReal 1) a b =
      affineMoment (N+10) (parityReal (-1)) a b := by
  apply Complex.ofReal_injective
  rw [affineMoment_complex_eq,affineMoment_complex_eq]
  simpa only [parityReal_cast, Complex.ofReal_one, Complex.ofReal_neg] using
    parityWeight_allDataEqual N a b

/-- Every odd-length literal translated moment of the real parity family vanishes. -/
theorem translatedMoment_parityReal_zero (N : ℕ) (t : ℝ) (m : ℕ)
    (h : Fin (2*m+1) → ℕ) : translatedMoment (N+10) (parityReal t) h = 0 := by
  apply Complex.ofReal_injective
  rw [translatedMoment_complex_eq]
  simp_rw [parityReal_cast]
  simpa only [Complex.ofReal_zero] using
    translationMoment_parityWeight N (t : ℂ) m (fun i => (h i : ZMod (N+10).factorial))

/-- The joint affine and all-odd observation family misses even absolute pointwise amplitude. -/
theorem exists_same_affine_odd_data_distinct_absolute_origin (N : ℕ) :
    ∃ c e : ℕ → ℝ,
      (∀ a b, affineMoment (N+10) c a b = affineMoment (N+10) e a b) ∧
      (∀ (m : ℕ) (h : Fin (2*m+1) → ℕ),
        translatedMoment (N+10) c h = translatedMoment (N+10) e h) ∧
      sieveSeq (N+10) c 0 = 6 ∧ ∀ k, |sieveSeq (N+10) e k| ≤ 5 := by
  refine ⟨parityReal 1, parityReal (-1), parityReal_affineMoment_eq N, ?_, ?_, ?_⟩
  · intro m h
    rw [translatedMoment_parityReal_zero,translatedMoment_parityReal_zero]
  · norm_num [sieveSeq_parityReal]
  · intro k
    rw [sieveSeq_parityReal]
    by_cases h2 : 2 ∣ k <;> by_cases h3 : 3 ∣ k <;> by_cases h5 : 5 ∣ k <;>
      norm_num [h2,h3,h5]

/-- No decoder from all affine quadratic and odd translated data recovers absolute origin response. -/
theorem no_absolute_origin_decoder_from_affine_and_odd (N : ℕ) :
    ¬∃ decode : ((ℕ → ℕ → ℝ) × ((m : ℕ) → (Fin (2*m+1) → ℕ) → ℝ)) → ℝ,
      ∀ c : ℕ → ℝ,
        decode (affineMoment (N+10) c, fun _ h => translatedMoment (N+10) c h) =
          |sieveSeq (N+10) c 0| := by
  obtain ⟨c,e,hA,hO,hc,he⟩ := exists_same_affine_odd_data_distinct_absolute_origin N
  rintro ⟨decode,hd⟩
  have hdata : (affineMoment (N+10) c, fun (m : ℕ) (h : Fin (2*m+1) → ℕ) =>
      translatedMoment (N+10) c h) =
      (affineMoment (N+10) e, fun (m : ℕ) (h : Fin (2*m+1) → ℕ) =>
      translatedMoment (N+10) e h) := by
    apply Prod.ext
    · funext a b
      exact hA a b
    · funext m h
      exact hO m h
  have habs : |sieveSeq (N+10) c 0| = |sieveSeq (N+10) e 0| := by
    rw [← hd c,← hd e,hdata]
  rw [hc] at habs
  have he0 := he 0
  norm_num at habs
  linarith only [habs,he0]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
