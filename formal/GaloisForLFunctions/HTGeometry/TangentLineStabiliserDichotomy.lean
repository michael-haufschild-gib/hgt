import GaloisForLFunctions.HTGeometry.DifferentialTangentSubmodule
import GaloisForLFunctions.HTGeometry.DerivationIterateLeibniz

/-!
# The line-stabiliser dichotomy for a differential-algebraic tangent space

The tangent space of a differential algebraic set at a point of it is cut out by the
*linearisations* of the defining differential polynomials, and a linearisation is a linear
differential form in the perturbation.  Substituting `c · Y` for a fixed direction `Y` and a scalar
`c` therefore produces, by the Leibniz rule, a **linear differential operator in `c`**:

```
    linearisationForm p P s (c · Y)  =  ∑_{k ≤ N} b k · δ^k c ,
```

with coefficients `b k` built from the partial derivatives of `P` at `p` and the jets of `Y`.  Two
things can happen.  Either every coefficient of every member of the family vanishes — and then the
whole `U`-line through `Y` is tangent — or one coefficient survives, and then the scalars whose
multiple of `Y` is tangent solve one *monic* scalar linear differential equation.

That dichotomy is exactly what removes the finite-dimensionality hypothesis from Cassidy's
classification of `sl₂`: `cassidy_sl2_of_differentialSolution` asks for the line stabilisers to be
solution sets of monic operators, and the alternative branch is handled by `sl2_eq_of_absorbing`.

* `differentialJet_mul_leibniz` — the binomial Leibniz rule for the algebraic jets;
* `exists_linearOperator_linearisationForm_smul` — the linear operator in the scalar;
* `exists_monic_of_linearOperator` — a nonzero coefficient makes it monic;
* `tangent_lineStabiliser_dichotomy` — the dichotomy.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [CommRing C] [Differential C] {ι : Type*}

/-- The binomial Leibniz rule for the algebraic jets, indexed by the order on the first factor. -/
theorem differentialJet_mul_leibniz (n : ℕ) (x y : C) :
    differentialJet n (x * y)
      = ∑ k ∈ Finset.range (n + 1),
          (n.choose k : C) * (differentialJet k x * differentialJet (n - k) y) := by
  have h := derivation_iterate_mul (R := ℤ) (A := C) Differential.deriv x y n
  rw [show differentialJet n (x * y) = (⇑(Differential.deriv : Derivation ℤ C C))^[n] (x * y) from
    rfl, h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsmul_eq_mul]
  rfl

/-- **The linearisation along a fixed direction is a linear differential operator in the scalar.**
Substituting `c · Y` into the linearisation of `P` at `p` produces `∑_{k ≤ N} b k · δ^k c` with
coefficients `b k` independent of `c`. -/
theorem exists_linearOperator_linearisationForm_smul
    (p : ι → C) (P : DifferentialPolynomial ι C) (s : Finset (ι × ℕ)) (Y : ι → C) :
    ∃ (N : ℕ) (b : ℕ → C), ∀ c : C,
      linearisationForm p P s (fun q => c * Y q)
        = ∑ k ∈ Finset.range (N + 1), b k * differentialJet k c := by
  classical
  set N : ℕ := s.sup (fun v => v.2) with hN
  set d : ι × ℕ → C := fun v => differentialPolynomialEvalOver (K := C) p
    (MvPolynomial.pderiv v P) with hd
  refine ⟨N, fun k => ∑ v ∈ s, (if k ≤ v.2 then
      (v.2.choose k : C) * (d v * differentialJet (v.2 - k) (Y v.1)) else 0), fun c => ?_⟩
  rw [linearisationForm]
  have hterm : ∀ v ∈ s, d v * differentialJet v.2 (c * Y v.1)
      = ∑ k ∈ Finset.range (N + 1),
          (if k ≤ v.2 then (v.2.choose k : C) * (d v * differentialJet (v.2 - k) (Y v.1)) else 0)
            * differentialJet k c := by
    intro v hv
    have hvN : v.2 ≤ N := Finset.le_sup (f := fun w : ι × ℕ => w.2) hv
    rw [differentialJet_mul_leibniz, Finset.mul_sum]
    have hsub : Finset.range (v.2 + 1) ⊆ Finset.range (N + 1) := by
      intro k hk
      exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (by omega))
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ v.2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [if_pos hk']
      ring
    · intro k _ hk
      have hk' : ¬ k ≤ v.2 := fun h => hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
      rw [if_neg hk', zero_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]

section Field

variable {C : Type*} [Field C] [Differential C] {ι : Type*}

/-- A linear differential relation with a nonzero coefficient can be made monic. -/
theorem exists_monic_of_linearOperator {N : ℕ} (b : ℕ → C) {T : Set C}
    (hT : ∀ c ∈ T, ∑ k ∈ Finset.range (N + 1), b k * differentialJet k c = 0)
    {k₀ : ℕ} (hk₀ : k₀ ∈ Finset.range (N + 1)) (hbk₀ : b k₀ ≠ 0) :
    ∃ (n : ℕ) (a : Fin n → C), ∀ c ∈ T,
      differentialJet n c = ∑ i, a i * differentialJet (i : ℕ) c := by
  classical
  set t : Finset ℕ := (Finset.range (N + 1)).filter (fun k => b k ≠ 0) with ht
  have htne : t.Nonempty := ⟨k₀, Finset.mem_filter.mpr ⟨hk₀, hbk₀⟩⟩
  set n : ℕ := t.max' htne with hn
  have hnmem : n ∈ t := t.max'_mem htne
  have hbn : b n ≠ 0 := (Finset.mem_filter.mp hnmem).2
  have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hnmem).1)
  have hzero : ∀ k, k ≤ N → n < k → b k = 0 := by
    intro k hkN hnk
    by_contra hbk
    have hk : k ∈ t := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hbk⟩
    exact absurd (t.le_max' k hk) (by omega)
  refine ⟨n, fun i => -(b i) / b n, fun c hc => ?_⟩
  have h := hT c hc
  have hsub : Finset.range (n + 1) ⊆ Finset.range (N + 1) := by
    intro k hk
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (by omega))
  have h2 : ∑ k ∈ Finset.range (n + 1), b k * differentialJet k c = 0 := by
    rw [Finset.sum_subset hsub ?_]
    · exact h
    · intro k hk hk'
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hnk : n < k := by
        by_contra hcon
        exact hk' (Finset.mem_range.mpr (by omega))
      rw [hzero k hkN hnk, zero_mul]
  rw [Finset.sum_range_succ] at h2
  have hs : ∑ k ∈ Finset.range n, b k * differentialJet k c = -(b n * differentialJet n c) :=
    eq_neg_of_add_eq_zero_left h2
  rw [Fin.sum_univ_eq_sum_range (fun i => (-(b i) / b n) * differentialJet i c) n]
  have key : ∑ k ∈ Finset.range n, (-(b k) / b n) * differentialJet k c
      = -(b n)⁻¹ * ∑ k ∈ Finset.range n, (b k * differentialJet k c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [key, hs]
  field_simp

/-- **The line-stabiliser dichotomy.**  For a direction `Y`, either every scalar multiple of `Y` is
a tangent direction of the family `S` at `p`, or the scalars whose multiple is a tangent direction
solve one monic scalar linear differential equation. -/
theorem tangent_lineStabiliser_dichotomy (p : ι → C) (S : Set (DifferentialPolynomial ι C))
    (Y : ι → C) :
    (∀ c : C, ∀ P ∈ S, linearisationForm p P P.vars (fun q => c * Y q) = 0)
    ∨ ∃ (n : ℕ) (a : Fin n → C),
        ∀ c : C, (∀ P ∈ S, linearisationForm p P P.vars (fun q => c * Y q) = 0) →
          differentialJet n c = ∑ i, a i * differentialJet (i : ℕ) c := by
  classical
  by_cases hall : ∀ c : C, ∀ P ∈ S, linearisationForm p P P.vars (fun q => c * Y q) = 0
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨c₀, P, hP, hne⟩ := hall
    obtain ⟨N, b, hb⟩ := exists_linearOperator_linearisationForm_smul p P P.vars Y
    have hk₀ : ∃ k ∈ Finset.range (N + 1), b k ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      rw [hb c₀]
      exact Finset.sum_eq_zero fun k hk => by rw [hcon k hk, zero_mul]
    obtain ⟨k₀, hk₀mem, hk₀ne⟩ := hk₀
    refine exists_monic_of_linearOperator (T := {c : C |
      ∀ P ∈ S, linearisationForm p P P.vars (fun q => c * Y q) = 0}) b ?_ hk₀mem hk₀ne
    intro c hc
    rw [← hb c]
    exact hc P hP

end Field

end

end GaloisForLFunctions.HTGeometry
