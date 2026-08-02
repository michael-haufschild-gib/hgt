import GaloisForLFunctions.HTGeometry.PureFibreUnramified
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The differential of the observation map is an isomorphism at a pure point

The perturbations of a factorisation that stay inside the critical range form the space
`degreeLT m × degreeLT n`, of dimension `m + n = L`; the inversion error over the horizon lives in
`degreeLT L`, also of dimension `L`.  The differential

`(dA, dB)  |->  (dA B + A dB)  mod  t^L`

between them is injective at a pure point, and therefore — the two spaces having the same finite
dimension — bijective.

Bijectivity is what makes a deformation of the observation solvable: every Newton step of a
deformation has a unique correction, so the pure fibre deforms with the observation.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- The space of perturbations that stay inside the critical range. -/
abbrev fibreTangentSpace (K : Type*) [Field K] (m n : ℕ) :=
  (degreeLT K m) × (degreeLT K n)

instance finiteDimensional_degreeLT (n : ℕ) : FiniteDimensional K (degreeLT K n) :=
  (degreeLTEquiv K n).symm.finiteDimensional

theorem finrank_degreeLT (n : ℕ) : Module.finrank K (degreeLT K n) = n := by
  rw [(degreeLTEquiv K n).finrank_eq, Module.finrank_fin_fun]

/-- **The differential of the observation map at a factorisation.** -/
noncomputable def fibreDifferential (A B : K[X]) (m n L : ℕ) :
    fibreTangentSpace K m n →ₗ[K] degreeLT K L where
  toFun p := ⟨((p.1 : K[X]) * B + A * (p.2 : K[X])) %ₘ X ^ L, by
    rw [mem_degreeLT]
    have hlt := degree_modByMonic_lt ((p.1 : K[X]) * B + A * (p.2 : K[X]))
      (monic_X_pow (R := K) L)
    rwa [degree_X_pow] at hlt⟩
  map_add' p q := by
    refine Subtype.ext ?_
    show (((p.1 : K[X]) + (q.1 : K[X])) * B + A * ((p.2 : K[X]) + (q.2 : K[X]))) %ₘ X ^ L = _
    rw [show ((p.1 : K[X]) + (q.1 : K[X])) * B + A * ((p.2 : K[X]) + (q.2 : K[X]))
        = ((p.1 : K[X]) * B + A * (p.2 : K[X])) + ((q.1 : K[X]) * B + A * (q.2 : K[X])) by ring,
      Polynomial.add_modByMonic]
    rfl
  map_smul' c p := by
    refine Subtype.ext ?_
    show ((c • (p.1 : K[X])) * B + A * (c • (p.2 : K[X]))) %ₘ X ^ L = _
    rw [show (c • (p.1 : K[X])) * B + A * (c • (p.2 : K[X]))
        = c • ((p.1 : K[X]) * B + A * (p.2 : K[X])) by
          simp only [Polynomial.smul_eq_C_mul]; ring,
      Polynomial.smul_modByMonic]
    rfl

theorem fibreDifferential_eq_zero_iff {A B : K[X]} {m n L : ℕ} {p : fibreTangentSpace K m n} :
    fibreDifferential A B m n L p = 0 ↔
      (X : K[X]) ^ L ∣ (p.1 : K[X]) * B + A * (p.2 : K[X]) := by
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd (monic_X_pow (R := K) L)]
  constructor
  · intro hcon
    exact congrArg Subtype.val hcon
  · intro hcon
    exact Subtype.ext hcon

/-- **The differential is injective at a pure point.** -/
theorem injective_fibreDifferential {m n : ℕ} {A B : K[X]} (hm : 0 < m) (hn : 0 < n)
    (hL : ((m + n : ℕ) : K) ≠ 0) (hAB : A * B = 1 + X ^ (m + n))
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n) :
    Function.Injective (fibreDifferential A B m n (m + n)) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro p hp
  have hdvd : (X : K[X]) ^ (m + n) ∣ (p.1 : K[X]) * B + A * (p.2 : K[X]) :=
    fibreDifferential_eq_zero_iff.1 hp
  have hdegA : ((p.1 : K[X])).natDegree < m := by
    rcases eq_or_ne ((p.1 : K[X])) 0 with h | h
    · rw [h, Polynomial.natDegree_zero]; omega
    · exact Polynomial.natDegree_lt_iff_degree_lt h |>.2 (mem_degreeLT.1 p.1.2)
  have hdegB : ((p.2 : K[X])).natDegree < n := by
    rcases eq_or_ne ((p.2 : K[X])) 0 with h | h
    · rw [h, Polynomial.natDegree_zero]; omega
    · exact Polynomial.natDegree_lt_iff_degree_lt h |>.2 (mem_degreeLT.1 p.2.2)
  obtain ⟨h1, h2⟩ :=
    tangent_eq_zero_of_pureFactorisation hm hn hL hAB hA hB hdegA hdegB hdvd
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

/-- **And therefore bijective**: the perturbation space and the error space both have dimension
`L = m + n`. -/
theorem bijective_fibreDifferential {m n : ℕ} {A B : K[X]} (hm : 0 < m) (hn : 0 < n)
    (hL : ((m + n : ℕ) : K) ≠ 0) (hAB : A * B = 1 + X ^ (m + n))
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n) :
    Function.Bijective (fibreDifferential A B m n (m + n)) := by
  have hdim : Module.finrank K (fibreTangentSpace K m n)
      = Module.finrank K (degreeLT K (m + n)) := by
    rw [Module.finrank_prod, finrank_degreeLT, finrank_degreeLT, finrank_degreeLT]
  have hinj := injective_fibreDifferential hm hn hL hAB hA hB
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj⟩

/-- **Every inversion error over the horizon is realised by a unique perturbation.**  This is the
solvability of one Newton step of a deformation of the critical observation. -/
theorem exists_unique_fibreDifferential {m n : ℕ} {A B : K[X]} (hm : 0 < m) (hn : 0 < n)
    (hL : ((m + n : ℕ) : K) ≠ 0) (hAB : A * B = 1 + X ^ (m + n))
    (hA : A.natDegree ≤ m) (hB : B.natDegree ≤ n) (E : degreeLT K (m + n)) :
    ∃! p : fibreTangentSpace K m n, fibreDifferential A B m n (m + n) p = E := by
  obtain ⟨hinj, hsurj⟩ := bijective_fibreDifferential hm hn hL hAB hA hB
  obtain ⟨p, hp⟩ := hsurj E
  exact ⟨p, hp, fun q hq => hinj (hq.trans hp.symm)⟩

end GaloisForLFunctions.HTGeometry
