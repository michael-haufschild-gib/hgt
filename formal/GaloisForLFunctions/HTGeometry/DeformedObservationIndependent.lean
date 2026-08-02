import GaloisForLFunctions.HTGeometry.PostcriticalNotRational
import GaloisForLFunctions.HTGeometry.ShiftedVariablesIndependent

/-!
# The deformed critical observation is algebraically independent

Under the universal deformation the critical observation of a jet reads

`1 + s_0, s_1, …, s_(n-1)`  on the raw side,  `1 + s_n, …, s_(L-1)` on the reciprocal side,

and the new raw coefficient is the last parameter `s_L`.  Each entry is one deformation parameter,
with a constant added in exactly two places, and the parameters are distinct.  So the deformed
observation is an affine change of the variables of the power series ring, hence algebraically
independent over the coefficient field.

This is the hypothesis a rational-function descent needs: the specialisation that sends the generic
observation to this one kills no nonzero polynomial in the observation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable (K : Type*) [Field K] (m n : ℕ)

theorem coeff_rawDeformation (k : Fin n) :
    (rawDeformation K m n).coeff (m + (k : ℕ)) = MvPowerSeries.X (Sum.inl k) := by
  classical
  rw [rawDeformation, Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg ?_, mul_zero]
    intro hcon
    exact hb (Fin.ext (by omega))
  · intro hc
    exact absurd (Finset.mem_univ k) hc

theorem coeff_reciprocalDeformation (k : Fin m) :
    (reciprocalDeformation K m n).coeff (n + (k : ℕ))
      = MvPowerSeries.X (Sum.inr (Sum.inl k)) := by
  classical
  rw [reciprocalDeformation, Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg ?_, mul_zero]
    intro hcon
    exact hb (Fin.ext (by omega))
  · intro hc
    exact absurd (Finset.mem_univ k) hc

variable {K m n}

/-- The reindexing of the observation coordinates by the deformation parameters. -/
def observationParam (m n : ℕ) : Fin (n + 1) ⊕ Fin m → Fin n ⊕ Fin m ⊕ Unit
  | Sum.inl k => if h : (k : ℕ) < n then Sum.inl ⟨(k : ℕ), h⟩ else Sum.inr (Sum.inr ())
  | Sum.inr k => Sum.inr (Sum.inl k)

theorem observationParam_injective (m n : ℕ) : Function.Injective (observationParam m n) := by
  rintro (k | k) (l | l) h <;>
    simp only [observationParam] at h
  · split_ifs at h with hk hl hl <;>
      first
        | exact congrArg Sum.inl (Fin.ext (by simpa using h))
        | exact congrArg Sum.inl (Fin.ext (by omega))
  · split_ifs at h
    simp at h
  · split_ifs at h
    simp at h
  · exact congrArg Sum.inr (by simpa using h)

/-- The constants added to the deformation parameters by a monic pair. -/
def observationShift (m n : ℕ) : Fin (n + 1) ⊕ Fin m → K
  | Sum.inl k => if (k : ℕ) = 0 then 1 else 0
  | Sum.inr k => if (k : ℕ) = 0 then 1 else 0

/-- **The deformed observation is a shift of the deformation parameters.** -/
theorem criticalObservation_eq_shift (hn : 0 < n)
    {A₀ B₀ : K[X]} (hA₀ : A₀.Monic) (hA₀deg : A₀.natDegree = m)
    (hB₀ : B₀.Monic) (hB₀deg : B₀.natDegree = n)
    {Z₀ W₀ : (deformBase K m n)[X]}
    (hZdec : ∀ i, m ≤ i → Z₀.coeff i
      = (A₀.map (algebraMap K (deformBase K m n))).coeff i + (rawDeformation K m n).coeff i)
    (hWdec : ∀ j, n ≤ j → W₀.coeff j
      = (B₀.map (algebraMap K (deformBase K m n))).coeff j
        + (reciprocalDeformation K m n).coeff j) :
    criticalObservation m n Z₀ W₀ (deformParam K m n)
      = fun s => MvPowerSeries.X (observationParam m n s)
        + algebraMap K (deformBase K m n) (observationShift (K := K) m n s) := by
  funext s
  rcases s with k | k
  · show (if (k : ℕ) < n then Z₀.coeff (m + (k : ℕ)) else deformParam K m n) = _
    by_cases hk : (k : ℕ) < n
    · rw [if_pos hk, hZdec _ (by omega), Polynomial.coeff_map]
      show _ = MvPowerSeries.X (observationParam m n (Sum.inl k))
        + algebraMap K (deformBase K m n) (observationShift (K := K) m n (Sum.inl k))
      rw [show observationParam m n (Sum.inl k) = Sum.inl ⟨(k : ℕ), hk⟩ by
        simp only [observationParam, dif_pos hk],
        coeff_rawDeformation K m n ⟨(k : ℕ), hk⟩]
      show algebraMap K (deformBase K m n) (A₀.coeff (m + (k : ℕ)))
        + MvPowerSeries.X (Sum.inl (⟨(k : ℕ), hk⟩ : Fin n)) = _
      rw [add_comm]
      congr 1
      show algebraMap K (deformBase K m n) (A₀.coeff (m + (k : ℕ)))
        = algebraMap K (deformBase K m n) (if (k : ℕ) = 0 then 1 else 0)
      congr 1
      by_cases hk0 : (k : ℕ) = 0
      · rw [hk0, Nat.add_zero, if_pos rfl, ← hA₀deg, hA₀.coeff_natDegree]
      · rw [if_neg hk0, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    · rw [if_neg hk]
      show deformParam K m n = MvPowerSeries.X (observationParam m n (Sum.inl k))
        + algebraMap K (deformBase K m n) (observationShift (K := K) m n (Sum.inl k))
      rw [show observationParam m n (Sum.inl k) = Sum.inr (Sum.inr ()) by
        simp only [observationParam, dif_neg hk],
        show observationShift (K := K) m n (Sum.inl k) = 0 by
          simp only [observationShift]
          rw [if_neg (by omega)]]
      rw [map_zero, add_zero, deformParam]
  · show W₀.coeff (n + (k : ℕ)) = _
    rw [hWdec _ (by omega), Polynomial.coeff_map]
    show algebraMap K (deformBase K m n) (B₀.coeff (n + (k : ℕ)))
        + (reciprocalDeformation K m n).coeff (n + (k : ℕ))
      = MvPowerSeries.X (observationParam m n (Sum.inr k))
        + algebraMap K (deformBase K m n) (observationShift (K := K) m n (Sum.inr k))
    rw [show observationParam m n (Sum.inr k) = Sum.inr (Sum.inl k) from rfl,
      coeff_reciprocalDeformation K m n k, add_comm]
    congr 1
    show algebraMap K (deformBase K m n) (B₀.coeff (n + (k : ℕ)))
      = algebraMap K (deformBase K m n) (if (k : ℕ) = 0 then 1 else 0)
    congr 1
    by_cases hk0 : (k : ℕ) = 0
    · rw [hk0, Nat.add_zero, if_pos rfl, ← hB₀deg, hB₀.coeff_natDegree]
    · rw [if_neg hk0, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- **The deformed critical observation is algebraically independent.** -/
theorem algebraicIndependent_criticalObservation (hn : 0 < n)
    {A₀ B₀ : K[X]} (hA₀ : A₀.Monic) (hA₀deg : A₀.natDegree = m)
    (hB₀ : B₀.Monic) (hB₀deg : B₀.natDegree = n)
    {Z₀ W₀ : (deformBase K m n)[X]}
    (hZdec : ∀ i, m ≤ i → Z₀.coeff i
      = (A₀.map (algebraMap K (deformBase K m n))).coeff i + (rawDeformation K m n).coeff i)
    (hWdec : ∀ j, n ≤ j → W₀.coeff j
      = (B₀.map (algebraMap K (deformBase K m n))).coeff j
        + (reciprocalDeformation K m n).coeff j) :
    AlgebraicIndependent K (criticalObservation m n Z₀ W₀ (deformParam K m n)) := by
  rw [criticalObservation_eq_shift hn hA₀ hA₀deg hB₀ hB₀deg hZdec hWdec]
  exact algebraicIndependent_add_const
    (algebraicIndependent_mvPowerSeries_X.comp _ (observationParam_injective m n))
    (observationShift (K := K) m n)

end GaloisForLFunctions.HTGeometry
