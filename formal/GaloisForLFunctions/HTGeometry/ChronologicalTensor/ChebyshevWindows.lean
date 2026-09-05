import GaloisForLFunctions.HTGeometry.ChronologicalTensor.BinaryWindows
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Chebyshev families with unit monotone capacity

The shifted Chebyshev polynomial is homogenized in two gap variables using
finite windows. Its monotone capacity is exactly one, in every degree.
This gives a concrete family for testing universal enclosure bounds.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section

def shiftedChebyshev (d : ℕ) : Polynomial ℝ :=
  (Polynomial.Chebyshev.T ℝ (d : ℤ)).comp (Polynomial.C 2*Polynomial.X-Polynomial.C 1)

def chebyshevCoefficients (d : ℕ) : Fin (d+1) → ℝ :=
  binaryCoefficients (shiftedChebyshev d) d

theorem shiftedChebyshev_degree (d : ℕ) : (shiftedChebyshev d).natDegree = d := by
  rw [shiftedChebyshev,Polynomial.natDegree_comp,Polynomial.natDegree_sub_C,
    Polynomial.natDegree_C_mul (show (2 : ℝ) ≠ 0 by positivity),Polynomial.natDegree_X,
    Polynomial.Chebyshev.natDegree_T]
  simp

theorem shiftedChebyshev_eval (d : ℕ) (x : ℝ) :
    (shiftedChebyshev d).eval x = (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (2*x-1) := by
  simp [shiftedChebyshev,Polynomial.eval_comp]

theorem binary_chebyshev_radial (d : ℕ) (x t : ℝ) :
    familyValue (binaryWindows d) (chebyshevCoefficients d) ![t*x,t*(1-x)] =
      t^d*(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval (2*x-1) := by
  have h := binary_radial_value (shiftedChebyshev d) 0 x t
  rw [Nat.add_zero,shiftedChebyshev_degree] at h
  simpa only [shiftedChebyshev_eval,chebyshevCoefficients] using h

theorem binary_chebyshev_monotone_bound (d : ℕ) (g : Fin 2 → ℝ) :
    |familyValue (binaryWindows d) (chebyshevCoefficients d) (monotoneProbe g)| ≤ 1 := by
  let z := monotoneProbe g
  let S := z 0+z 1
  have hz0 : 0 ≤ z 0 := abs_nonneg _
  have hz1 : 0 ≤ z 1 := abs_nonneg _
  have hs0 : 0 ≤ S := add_nonneg hz0 hz1
  have hs1 : S ≤ 1 := by
    have h := monotoneProbe_budget g
    change variation z ≤ 1 at h
    rw [variation,Fin.sum_univ_two] at h
    rwa [abs_of_nonneg hz0,abs_of_nonneg hz1] at h
  have bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
      |familyValue (binaryWindows d) (chebyshevCoefficients d) ![S*x,S*(1-x)]| ≤ 1 := by
    rw [binary_chebyshev_radial,abs_mul,abs_pow,abs_of_nonneg hs0]
    have hc := Polynomial.Chebyshev.abs_eval_T_real_le_one (d : ℤ)
      (show |2*x-1| ≤ 1 by rw [abs_le]; constructor <;> linarith)
    have hp := pow_le_pow_left₀ hs0 hs1 d
    rw [one_pow] at hp
    exact (mul_le_mul hp hc (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  by_cases hs : S = 0
  · have hz : z = (![S*0,S*(1-0)] : Fin 2 → ℝ) := by
      have h0 : z 0 = 0 := by dsimp [S] at hs; linarith
      have h1 : z 1 = 0 := by dsimp [S] at hs; linarith
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [h0,hs]
      · have hj : j = 0 := Fin.eq_zero j
        subst j
        simp [h1,hs]
    change |familyValue (binaryWindows d) (chebyshevCoefficients d) z| ≤ 1
    rw [hz]
    exact bound 0 le_rfl (by positivity)
  · have hspos : 0 < S := lt_of_le_of_ne hs0 (Ne.symm hs)
    have hx0 : 0 ≤ z 0/S := div_nonneg hz0 hs0
    have hx1 : z 0/S ≤ 1 := (div_le_one hspos).mpr (by dsimp [S]; linarith)
    have hz : z = (![S*(z 0/S),S*(1-z 0/S)] : Fin 2 → ℝ) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Matrix.cons_val_zero]; field_simp
      · have hj : j = 0 := Fin.eq_zero j
        subst j
        change z 1 = S*(1-z 0/S)
        field_simp
        dsimp [S]
        ring
    change |familyValue (binaryWindows d) (chebyshevCoefficients d) z| ≤ 1
    rw [hz]
    exact bound _ hx0 hx1

theorem binary_chebyshev_monotoneCapacity (d : ℕ) :
    monotoneCapacity (binaryWindows d) (chebyshevCoefficients d) = 1 := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g,rfl⟩
    exact binary_chebyshev_monotone_bound d g
  · have hb := monotoneCapacity_probe_bound (binaryWindows d) (chebyshevCoefficients d)
        (![1,0] : Fin 2 → ℝ)
    have hg : monotoneProbe (![1,0] : Fin 2 → ℝ) = ![(1 : ℝ)*1,1*(1-1)] := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [monotoneProbe,normalizeProbe,variation,Fin.sum_univ_two]
      · have hj : j = 0 := Fin.eq_zero j
        subst j
        simp [monotoneProbe,normalizeProbe,variation,Fin.sum_univ_two]
    rw [hg,binary_chebyshev_radial] at hb
    simpa only [one_pow,mul_one,show (2 : ℝ)-1=1 by ring,
      Polynomial.Chebyshev.T_eval_one,one_mul,abs_one] using hb

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
