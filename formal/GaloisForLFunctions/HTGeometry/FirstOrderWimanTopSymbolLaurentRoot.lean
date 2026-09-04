import GaloisForLFunctions.HTGeometry.FirstOrderWimanTopSymbolPuiseuxRoot
import Mathlib.RingTheory.LaurentSeries

/-!
# Literal Laurent-series root of every Wiman top symbol

This file reverses the power-series clearing used by the prescribed Newton--Puiseux lift.  The
identities are proved term by term in `LaurentSeries ℂ`, so the constructed branch is a literal zero
of the complete Wiman top symbol after the finite cover `U = s⁻ᴺq`.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries Polynomial PowerSeries

noncomputable section

/-- Evaluation of the complete top face, retaining every coefficient monomial. -/
noncomputable def firstOrderTopSymbolLaurentValue
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ)
    (U T : LaurentSeries ℂ) : LaurentSeries ℂ :=
  ∑ i ∈ firstOrderTopNewtonFace S A d,
    ∑ n ∈ (A i).support,
      HahnSeries.single (0 : ℤ) ((A i).coeff n) * U ^ n * T ^ i.2

/-- Expanding a power-series monomial by `N` and embedding it into Laurent series gives the
corresponding Laurent monomial. -/
theorem algebraMap_expand_C_mul_X_pow
    (N e : ℕ) (hN : N ≠ 0) (c : ℂ) :
    algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
      (PowerSeries.expand N hN
        (PowerSeries.C c * (PowerSeries.X : PowerSeries ℂ) ^ e)) =
      HahnSeries.single ((N * e : ℕ) : ℤ) c := by
  change HahnSeries.ofPowerSeries ℤ ℂ
      (PowerSeries.expand N hN
        (PowerSeries.C c * (PowerSeries.X : PowerSeries ℂ) ^ e)) = _
  rw [map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X]
  rw [map_mul (HahnSeries.ofPowerSeries ℤ ℂ)]
  rw [HahnSeries.ofPowerSeries_C]
  have hXpow :
      (HahnSeries.ofPowerSeries ℤ ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ N) =
        (HahnSeries.single (1 : ℤ) (1 : ℂ)) ^ N := by
    rw [map_pow (HahnSeries.ofPowerSeries ℤ ℂ), HahnSeries.ofPowerSeries_X]
  have hpowE :
      (HahnSeries.ofPowerSeries ℤ ℂ) (((PowerSeries.X : PowerSeries ℂ) ^ N) ^ e) =
        ((HahnSeries.ofPowerSeries ℤ ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ N)) ^ e := by
    exact map_pow (HahnSeries.ofPowerSeries ℤ ℂ) _ e
  rw [hpowE, hXpow]
  rw [← pow_mul]
  induction N * e with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, HahnSeries.single_mul_single]
      simp

/-- Powers of a unit-coefficient Hahn monomial add their integer exponents. -/
theorem hahnSingleOne_pow_int (e : ℤ) (n : ℕ) :
    (HahnSeries.single e (1 : ℂ)) ^ n =
      HahnSeries.single ((n : ℤ) * e) 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, HahnSeries.single_mul_single]
      congr 1
      · push_cast
        ring_nf
      · simp

/-- One cleared Wiman monomial is exactly its substituted Laurent-series monomial multiplied by
the global clearing factor. -/
theorem firstOrderInfinity_laurent_term_identity
    (N q M H n k : ℕ) (hN : N ≠ 0) (c : ℂ) (Y : PowerSeries ℂ)
    (hbase : q * n + M * k ≤ H) :
    HahnSeries.single ((N * H : ℕ) : ℤ) (1 : ℂ) *
        (HahnSeries.single (0 : ℤ) c *
          (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ)) ^ n *
          (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
            algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) Y) ^ k) =
      algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
          (PowerSeries.expand N hN
            (PowerSeries.C c * (PowerSeries.X : PowerSeries ℂ) ^
              (H - (q * n + M * k)))) *
        (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) Y) ^ k := by
  rw [algebraMap_expand_C_mul_X_pow]
  rw [hahnSingleOne_pow_int, mul_pow, hahnSingleOne_pow_int]
  have hsingle :
      HahnSeries.single ((N * H : ℕ) : ℤ) (1 : ℂ) *
          HahnSeries.single ((n : ℤ) * -((N * q : ℕ) : ℤ)) c *
          HahnSeries.single ((k : ℤ) * -((N * M : ℕ) : ℤ)) 1 =
        HahnSeries.single ((N * (H - (q * n + M * k)) : ℕ) : ℤ) c := by
    rw [HahnSeries.single_mul_single, HahnSeries.single_mul_single]
    simp only [one_mul, mul_one]
    apply congrArg (fun e : ℤ => HahnSeries.single e c)
    push_cast
    rw [Nat.cast_sub hbase]
    push_cast
    ring
  rw [HahnSeries.single_mul_single]
  calc
    _ = (HahnSeries.single ((N * H : ℕ) : ℤ) (1 : ℂ) *
          HahnSeries.single ((n : ℤ) * -((N * q : ℕ) : ℤ)) c *
          HahnSeries.single ((k : ℤ) * -((N * M : ℕ) : ℤ)) 1) *
          (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) Y) ^ k := by noncomm_ring
    _ = _ := by rw [hsingle]

/-- Summing the monomial identity proves that the cleared polynomial evaluation is exactly the
original top-symbol evaluation times the global Laurent unit. -/
theorem firstOrderInfinity_laurentValue_mul_eq_clearedEval
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H N : ℕ)
    (hN : N ≠ 0) (Y : PowerSeries ℂ)
    (hbound : ∀ i ∈ firstOrderTopNewtonFace S A d, ∀ n ∈ (A i).support,
      q * n + M * i.2 ≤ H) :
    HahnSeries.single ((N * H : ℕ) : ℤ) (1 : ℂ) *
        firstOrderTopSymbolLaurentValue S A d
          (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ))
          (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
            algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) Y) =
      algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
        (((firstOrderInfinityPowerSeriesPolynomial S A d q M H).map
          (PowerSeries.expand (R := ℂ) N hN).toRingHom).eval Y) := by
  classical
  rw [firstOrderTopSymbolLaurentValue, Finset.mul_sum]
  rw [firstOrderInfinityPowerSeriesPolynomial]
  change (∑ i ∈ firstOrderTopNewtonFace S A d,
      HahnSeries.single ((N * H : ℕ) : ℤ) (1 : ℂ) *
        ∑ n ∈ (A i).support,
          HahnSeries.single (0 : ℤ) ((A i).coeff n) *
            HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ) ^ n *
            (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
              algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) Y) ^ i.2) =
    (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ))
      ((Polynomial.evalRingHom Y)
        ((Polynomial.mapRingHom (PowerSeries.expand (R := ℂ) N hN).toRingHom)
          (∑ i ∈ firstOrderTopNewtonFace S A d,
            ∑ n ∈ (A i).support,
              Polynomial.C (PowerSeries.C ((A i).coeff n) *
                (PowerSeries.X : PowerSeries ℂ) ^ (H - (q * n + M * i.2))) *
                  Polynomial.X ^ i.2)))
  rw [map_sum (Polynomial.mapRingHom (PowerSeries.expand (R := ℂ) N hN).toRingHom),
    map_sum (Polynomial.evalRingHom Y),
    map_sum (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  rw [map_sum (Polynomial.mapRingHom (PowerSeries.expand (R := ℂ) N hN).toRingHom),
    map_sum (Polynomial.evalRingHom Y),
    map_sum (algebraMap (PowerSeries ℂ) (LaurentSeries ℂ))]
  apply Finset.sum_congr rfl
  intro n hn
  change
    HahnSeries.single ((N * H : ℕ) : ℤ) (1 : ℂ) *
        (HahnSeries.single (0 : ℤ) ((A i).coeff n) *
          HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ) ^ n *
          (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
            algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) Y) ^ i.2) =
      algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
        (((Polynomial.C (PowerSeries.C ((A i).coeff n) *
            (PowerSeries.X : PowerSeries ℂ) ^ (H - (q * n + M * i.2))) *
              Polynomial.X ^ i.2).map
            (PowerSeries.expand (R := ℂ) N hN).toRingHom).eval Y)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, map_mul, map_pow]
  exact firstOrderInfinity_laurent_term_identity N q M H n i.2 hN
    ((A i).coeff n) Y (hbound i hi n hn)

/-- A root of the cleared polynomial gives a root of the original top symbol because its global
clearing factor is nonzero. -/
theorem firstOrderTopSymbolLaurentValue_eq_zero_of_clearedRoot
    (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d q M H N : ℕ)
    (hN : N ≠ 0) (Y : PowerSeries ℂ)
    (hbound : ∀ i ∈ firstOrderTopNewtonFace S A d, ∀ n ∈ (A i).support,
      q * n + M * i.2 ≤ H)
    (hroot : ((firstOrderInfinityPowerSeriesPolynomial S A d q M H).map
      (PowerSeries.expand (R := ℂ) N hN).toRingHom).IsRoot Y) :
    firstOrderTopSymbolLaurentValue S A d
        (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ))
        (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
          algebraMap (PowerSeries ℂ) (LaurentSeries ℂ) Y) = 0 := by
  have hproduct := firstOrderInfinity_laurentValue_mul_eq_clearedEval
    S A d q M H N hN Y hbound
  rw [hroot, map_zero] at hproduct
  exact (mul_eq_zero.mp hproduct).resolve_left (by simp)

/-- **Literal prescribed Wiman top-symbol root.**  Every exact Wiman package yields a literal zero
of its complete top symbol over the Laurent-series field after a finite ramified infinity cover.
The signed slope and prescribed nonzero leading coefficient are retained. -/
theorem exists_entireFirstOrderWiman_topSymbolLaurentRoot
    {f : ℂ → ℂ} (data : EntireFirstOrderWimanInitialData f) :
    ∃ (M a q N : ℕ) (_hN : N ≠ 0) (z : PowerSeries ℂ),
      q ≠ 0 ∧ data.slope = ((M : ℚ) - (a : ℚ)) / q ∧
      PowerSeries.constantCoeff z = data.root ∧
      firstOrderTopSymbolLaurentValue data.indexSupport data.coeff data.totalDegree
        (HahnSeries.single (-((N * q : ℕ) : ℤ)) (1 : ℂ))
        (HahnSeries.single (-((N * M : ℕ) : ℤ)) (1 : ℂ) *
          algebraMap (PowerSeries ℂ) (LaurentSeries ℂ)
            ((PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z)) = 0 := by
  obtain ⟨M, a, q, m, H, N, hN, z, hq, hp, hbound, hdegree, hspecial, hroot, hz⟩ :=
    exists_entireFirstOrderWiman_topSymbolPuiseuxRoot data
  let Y := (PowerSeries.X : PowerSeries ℂ) ^ (N * a) * z
  refine ⟨M, a, q, N, hN, z, hq, hp, hz, ?_⟩
  exact firstOrderTopSymbolLaurentValue_eq_zero_of_clearedRoot
    data.indexSupport data.coeff data.totalDegree q M H N hN Y hbound hroot

end

end GaloisForLFunctions.HTGeometry
