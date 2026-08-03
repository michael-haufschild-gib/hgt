import GaloisForLFunctions.HTGeometry.ShiftInvariantTelescoper
import GaloisForLFunctions.HTGeometry.DifferenceDifferential

/-!
# Differential dependence of indefinite sums forces a telescoper

Let `L` carry a derivation and an automorphism `σ` commuting with it, and let `K` be a differential
subfield stable under `σ`.  If `y₁,…,y_m ∈ L` solve the indefinite-sum equations

```text
σ(yᵢ) - yᵢ = rᵢ ∈ K,
```

then the ideal of polynomial relations satisfied by the jets `δ^k yᵢ` over `K` is stable under the
operator `Φ(P) = P^σ(X + R)`, where `R` collects the jets `δ^k rᵢ`: applying `σ` to a relation is
exactly applying `Φ` to the relating polynomial, because

```text
σ(δ^k yᵢ) = δ^k yᵢ + δ^k rᵢ.
```

The relation ideal contains no nonzero constant, since `K` embeds in `L`.  The descent therefore
applies, and a differential relation among the `yᵢ` produces constants `a_{i,k}` fixed by `σ`, not
all zero, and `g ∈ K` with

```text
∑_{i,k} a_{i,k} δ^k rᵢ = σg - g.
```

Contrapositively, a family of indefinite sums whose defects admit no such telescoper is
differentially independent.  This is the criterion a hypertranscendence proof for the digamma-type
functions consumes: the analytic input is reduced to the summability of one rational combination.
-/

open scoped BigOperators Differential

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Differential K] [Differential L]
  [DifferentialAlgebra K L]

/-- A difference automorphism commuting with the derivation commutes with every jet. -/
theorem aut_differentialJet_of_comm (σL : L ≃+* L) (hcomm : ∀ x : L, σL (x′) = (σL x)′)
    (n : ℕ) (x : L) : σL (differentialJet n x) = differentialJet n (σL x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [differentialJet_succ, differentialJet_succ, hcomm, ih]

/-- **Differential dependence of indefinite sums produces a telescoper.**  A polynomial relation
among the jets of solutions of `σy - y = r` yields a nonzero family of `σ`-invariant constants whose
combination of the jets of the defects is a `σ`-coboundary. -/
theorem exists_telescoper_of_not_differentialIndependent [CharZero K]
    (σK : K →+* K) (σL : L ≃+* L) (hcomm : ∀ x : L, σL (x′) = (σL x)′)
    (hbase : ∀ c : K, σL (algebraMap K L c) = algebraMap K L (σK c))
    {m : Type*} [DecidableEq m] (y : m → L) (r : m → K)
    (hy : ∀ i, σL (y i) - y i = algebraMap K L (r i))
    (hdep : ¬ DifferentialIndependent K y) :
    ∃ (s : Finset (m × ℕ)) (a : m × ℕ → K) (g : K),
      (∃ p ∈ s, a p ≠ 0) ∧ (∀ p : m × ℕ, σK (a p) = a p) ∧
        ∑ p ∈ s, a p * differentialJet p.2 (r p.1) = σK g - g := by
  classical
  set jet : m × ℕ → L := fun p => differentialJet p.2 (y p.1) with hjetdef
  set R : m × ℕ → K := fun p => differentialJet p.2 (r p.1) with hRdef
  have hdefect : ∀ p : m × ℕ, σL (jet p) - jet p = algebraMap K L (R p) := by
    intro p
    rw [hjetdef, hRdef, aut_differentialJet_of_comm σL hcomm, ← differentialJet_sub, hy p.1,
      differentialJet_algebraMap_apply]
  set F : MvPolynomial (m × ℕ) K →+* L := MvPolynomial.eval₂Hom (algebraMap K L) jet with hFdef
  have hFC : ∀ c : K, F (C c) = algebraMap K L c := by
    intro c
    rw [hFdef]
    exact MvPolynomial.eval₂Hom_C _ _ c
  have hFX : ∀ p : m × ℕ, F (X p) = jet p := by
    intro p
    rw [hFdef]
    exact MvPolynomial.eval₂Hom_X' _ _ p
  have hFaeval : ∀ P : MvPolynomial (m × ℕ) K, F P = MvPolynomial.aeval jet P := by
    intro P
    rw [hFdef, MvPolynomial.aeval_def]
    rfl
  have hphi : ∀ P : MvPolynomial (m × ℕ) K, F (shiftTranslate σK R P) = σL (F P) := by
    have hhom : F.comp (shiftTranslate σK R) = (σL : L →+* L).comp F := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun p => ?_)
      · simp only [RingHom.comp_apply, shiftTranslate_C, hFC]
        exact (hbase c).symm
      · simp only [RingHom.comp_apply, shiftTranslate_X, map_add, hFC, hFX]
        rw [← hdefect p]
        show jet p + (σL (jet p) - jet p) = σL (jet p)
        ring
    exact fun P => RingHom.congr_fun hhom P
  set J : Ideal (MvPolynomial (m × ℕ) K) := RingHom.ker F with hJdef
  have hJ : ∀ P ∈ J, shiftTranslate σK R P ∈ J := by
    intro P hP
    rw [hJdef, RingHom.mem_ker] at hP ⊢
    rw [hphi, hP, map_zero]
  have hJC : ∀ c : K, C c ∈ J → c = 0 := by
    intro c hc
    rw [hJdef, RingHom.mem_ker, hFC] at hc
    exact (algebraMap K L).injective (by rw [hc, map_zero])
  obtain ⟨P, hPJ, hP0⟩ : ∃ P : MvPolynomial (m × ℕ) K, F P = 0 ∧ P ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hdep ((algebraicIndependent_iff (x := jet)).mpr fun p hp => hcon p ?_)
    rw [hFaeval]
    exact hp
  exact exists_telescoper_of_mem_ideal σK R J hJ hJC (by rw [hJdef, RingHom.mem_ker]; exact hPJ) hP0

end

end GaloisForLFunctions
