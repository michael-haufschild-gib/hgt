import GaloisForLFunctions.HTGeometry.PrincipalSymbolHypertranscendenceHorizon
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Graded principal-symbol hypertranscendence horizon

A filtered derivation may have a different principal raising coefficient at every layer.  Its
complete cyclic jet is algebraically independent exactly when none of those graded symbols
vanishes.  If one layer symbol vanishes, that finite filtration layer becomes invariant and traps
the complete future jet.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Module Set

variable {k K L : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

/-- Product of the principal raising symbols strictly below layer `n`. -/
def gradedPrincipalProduct (symbol : ℕ → K) (n : ℕ) : K :=
  ∏ j ∈ Finset.range n, symbol j

@[simp]
theorem gradedPrincipalProduct_zero (symbol : ℕ → K) :
    gradedPrincipalProduct symbol 0 = 1 := by
  simp [gradedPrincipalProduct]

theorem gradedPrincipalProduct_succ (symbol : ℕ → K) (n : ℕ) :
    gradedPrincipalProduct symbol (n + 1) =
      gradedPrincipalProduct symbol n * symbol n := by
  simp [gradedPrincipalProduct, Finset.prod_range_succ]

/-- A compatible derivation raises the strict source filtration by at most one layer when its
principal coefficient is allowed to vary with the layer. -/
theorem derivation_principalFiltration_succ_graded
    (D₀ : Derivation k K K) (D : Derivation k L L) (u : ℕ → L)
    (symbol : ℕ → K)
    (hcompat : ∀ a : K, D (algebraMap K L a) = algebraMap K L (D₀ a))
    (hstep : ∀ n : ℕ,
      D (u n) - symbol n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1))
    (n : ℕ) {y : L} (hy : y ∈ principalFiltration (K := K) u n) :
    D y ∈ principalFiltration (K := K) u (n + 1) := by
  refine Submodule.span_induction
    (R := K) (M := L) (s := Set.range fun j : Fin n ↦ u j)
    (p := fun y _ ↦ D y ∈ principalFiltration (K := K) u (n + 1))
    ?_ ?_ ?_ ?_ (hx := hy)
  · rintro y ⟨j, rfl⟩
    have hjn : (j : ℕ) < n := j.isLt
    have hrem : D (u j) - symbol j • u ((j : ℕ) + 1) ∈
        principalFiltration (K := K) u (n + 1) :=
      principalFiltration_mono (K := K) u
        (Nat.succ_le_succ (Nat.le_of_lt hjn)) (hstep j)
    have hlead : symbol j • u ((j : ℕ) + 1) ∈
        principalFiltration (K := K) u (n + 1) :=
      (principalFiltration (K := K) u (n + 1)).smul_mem (symbol j)
        (principalFiltration_source_mem (K := K) u (Nat.succ_lt_succ hjn))
    simpa only [sub_add_cancel] using
      (principalFiltration (K := K) u (n + 1)).add_mem hrem hlead
  · simp
  · intro x y hx hy hxD hyD
    simpa using (principalFiltration (K := K) u (n + 1)).add_mem hxD hyD
  · intro a y hy hyD
    rw [Algebra.smul_def, Derivation.leibniz, hcompat]
    have haDy := (principalFiltration (K := K) u (n + 1)).smul_mem a hyD
    have hD₀y := (principalFiltration (K := K) u (n + 1)).smul_mem (D₀ a)
      (principalFiltration_mono (K := K) u (Nat.le_succ n) hy)
    simpa [Algebra.smul_def, mul_comm] using
      (principalFiltration (K := K) u (n + 1)).add_mem haDy hD₀y

/-- The `n`-th jet has leading source term equal to the product of all preceding layer symbols. -/
theorem gradedPrincipalJet_sub_product_smul_mem
    (D₀ : Derivation k K K) (D : Derivation k L L) (u : ℕ → L)
    (symbol : ℕ → K)
    (hcompat : ∀ a : K, D (algebraMap K L a) = algebraMap K L (D₀ a))
    (hstep : ∀ n : ℕ,
      D (u n) - symbol n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1)) :
    ∀ n : ℕ,
      ((D : L → L)^[n] (u 0)) - gradedPrincipalProduct symbol n • u n ∈
        principalFiltration (K := K) u n := by
  intro n
  induction n with
  | zero => simp [principalFiltration]
  | succ n ih =>
      let r : L := ((D : L → L)^[n] (u 0)) -
        gradedPrincipalProduct symbol n • u n
      have hr : r ∈ principalFiltration (K := K) u n := ih
      have hDr : D r ∈ principalFiltration (K := K) u (n + 1) :=
        derivation_principalFiltration_succ_graded
          D₀ D u symbol hcompat hstep n hr
      have hDn : D (u n) - symbol n • u (n + 1) ∈
          principalFiltration (K := K) u (n + 1) := hstep n
      have hcoeff : (D₀ (gradedPrincipalProduct symbol n)) • u n ∈
          principalFiltration (K := K) u (n + 1) :=
        (principalFiltration (K := K) u (n + 1)).smul_mem _
          (principalFiltration_source_mem (K := K) u (Nat.lt_succ_self n))
      have hscaled : gradedPrincipalProduct symbol n •
          (D (u n) - symbol n • u (n + 1)) ∈
          principalFiltration (K := K) u (n + 1) :=
        (principalFiltration (K := K) u (n + 1)).smul_mem _ hDn
      have hsum := (principalFiltration (K := K) u (n + 1)).add_mem
        ((principalFiltration (K := K) u (n + 1)).add_mem hDr hcoeff) hscaled
      rw [Function.iterate_succ_apply']
      have hrEq : ((D : L → L)^[n] (u 0)) =
          r + gradedPrincipalProduct symbol n • u n := by
        exact (sub_add_cancel _ _).symm
      rw [hrEq, map_add, Algebra.smul_def, Derivation.leibniz, hcompat]
      convert hsum using 1 <;>
        simp [Algebra.smul_def, gradedPrincipalProduct_succ] <;> ring

/-- Every finite jet packet is algebraically independent when every layer symbol before it is
nonzero. -/
theorem gradedPrincipalJetPacket_algebraicIndependent
    (D₀ : Derivation k K K) (D : Derivation k L L) (u : ℕ → L)
    (symbol : ℕ → K)
    (hcompat : ∀ a : K, D (algebraMap K L a) = algebraMap K L (D₀ a))
    (hstep : ∀ n : ℕ,
      D (u n) - symbol n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1))
    (hsymbol : ∀ n, symbol n ≠ 0) (N : ℕ)
    (hu : AlgebraicIndependent K (fun i : Fin N ↦ u i)) :
    AlgebraicIndependent K (fun i : Fin N ↦ (D : L → L)^[(i : ℕ)] (u 0)) := by
  apply algebraicIndependent_of_lowerTriangularSpan
    (fun i : Fin N ↦ u i)
    (fun i : Fin N ↦ (D : L → L)^[(i : ℕ)] (u 0))
    (fun i : Fin N ↦ gradedPrincipalProduct symbol i) hu
  · intro i
    simpa [principalFiltration] using
      gradedPrincipalJet_sub_product_smul_mem D₀ D u symbol hcompat hstep (i : ℕ)
  · intro i
    exact Finset.prod_ne_zero_iff.mpr (fun j _ ↦ hsymbol j)

/-- If no graded principal symbol vanishes, the complete cyclic jet is algebraically independent. -/
theorem gradedPrincipalJet_algebraicIndependent
    (D₀ : Derivation k K K) (D : Derivation k L L) (u : ℕ → L)
    (symbol : ℕ → K)
    (hcompat : ∀ a : K, D (algebraMap K L a) = algebraMap K L (D₀ a))
    (hstep : ∀ n : ℕ,
      D (u n) - symbol n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1))
    (hsymbol : ∀ n, symbol n ≠ 0) (hu : AlgebraicIndependent K u) :
    AlgebraicIndependent K (fun n : ℕ ↦ (D : L → L)^[n] (u 0)) := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  letI : Fintype t := ht.fintype
  let N : ℕ := t.toFinset.sup id + 1
  let e : t → Fin N := fun i ↦
    ⟨i.1, Nat.lt_succ_of_le (Finset.le_sup (f := id)
      (show i.1 ∈ t.toFinset by simpa using i.2))⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext_iff.mp hij
  have huN : AlgebraicIndependent K (fun i : Fin N ↦ u i) :=
    hu.comp (fun i : Fin N ↦ (i : ℕ)) Fin.val_injective
  have hN := gradedPrincipalJetPacket_algebraicIndependent
    D₀ D u symbol hcompat hstep hsymbol N huN
  simpa [e, Function.comp_def] using hN.comp e he

/-- If the symbol at layer `m` vanishes, the filtration through `u_m` is invariant under the
derivation. -/
theorem derivation_principalFiltration_invariant_of_gradedSymbol_eq_zero
    (D₀ : Derivation k K K) (D : Derivation k L L) (u : ℕ → L)
    (symbol : ℕ → K)
    (hcompat : ∀ a : K, D (algebraMap K L a) = algebraMap K L (D₀ a))
    (hstep : ∀ n : ℕ,
      D (u n) - symbol n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1))
    (m : ℕ) (hm : symbol m = 0) {y : L}
    (hy : y ∈ principalFiltration (K := K) u (m + 1)) :
    D y ∈ principalFiltration (K := K) u (m + 1) := by
  refine Submodule.span_induction
    (R := K) (M := L) (s := Set.range fun j : Fin (m + 1) ↦ u j)
    (p := fun y _ ↦ D y ∈ principalFiltration (K := K) u (m + 1))
    ?_ ?_ ?_ ?_ (hx := hy)
  · rintro y ⟨j, rfl⟩
    have hrem : D (u j) - symbol j • u ((j : ℕ) + 1) ∈
        principalFiltration (K := K) u (m + 1) :=
      principalFiltration_mono (K := K) u
        (Nat.succ_le_succ (Nat.le_of_lt_succ j.isLt)) (hstep j)
    have hlead : symbol j • u ((j : ℕ) + 1) ∈
        principalFiltration (K := K) u (m + 1) := by
      by_cases hj : (j : ℕ) = m
      · rw [hj, hm, zero_smul]
        exact (principalFiltration (K := K) u (m + 1)).zero_mem
      · have hjm : (j : ℕ) < m := by omega
        exact (principalFiltration (K := K) u (m + 1)).smul_mem (symbol j)
          (principalFiltration_source_mem (K := K) u (Nat.succ_lt_succ hjm))
    simpa only [sub_add_cancel] using
      (principalFiltration (K := K) u (m + 1)).add_mem hrem hlead
  · simp
  · intro x y hx hy hxD hyD
    simpa using (principalFiltration (K := K) u (m + 1)).add_mem hxD hyD
  · intro a y hy hyD
    rw [Algebra.smul_def, Derivation.leibniz, hcompat]
    have haDy := (principalFiltration (K := K) u (m + 1)).smul_mem a hyD
    have hD₀y := (principalFiltration (K := K) u (m + 1)).smul_mem (D₀ a) hy
    simpa [Algebra.smul_def, mul_comm] using
      (principalFiltration (K := K) u (m + 1)).add_mem haDy hD₀y

/-- A vanished layer symbol traps every later jet in the corresponding finite source filtration. -/
theorem gradedPrincipalJet_mem_of_symbol_eq_zero
    (D₀ : Derivation k K K) (D : Derivation k L L) (u : ℕ → L)
    (symbol : ℕ → K)
    (hcompat : ∀ a : K, D (algebraMap K L a) = algebraMap K L (D₀ a))
    (hstep : ∀ n : ℕ,
      D (u n) - symbol n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1))
    (m : ℕ) (hm : symbol m = 0) :
    ∀ n : ℕ,
      (D : L → L)^[n] (u 0) ∈ principalFiltration (K := K) u (m + 1) := by
  intro n
  induction n with
  | zero =>
      exact principalFiltration_source_mem (K := K) u (Nat.zero_lt_succ m)
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact derivation_principalFiltration_invariant_of_gradedSymbol_eq_zero
        D₀ D u symbol hcompat hstep m hm ih

/-- One vanished layer symbol forces algebraic dependence of the complete cyclic jet. -/
theorem not_algebraicIndependent_gradedPrincipalJet_of_symbol_eq_zero
    (D₀ : Derivation k K K) (D : Derivation k L L) (u : ℕ → L)
    (symbol : ℕ → K)
    (hcompat : ∀ a : K, D (algebraMap K L a) = algebraMap K L (D₀ a))
    (hstep : ∀ n : ℕ,
      D (u n) - symbol n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1))
    (m : ℕ) (hm : symbol m = 0) :
    ¬ AlgebraicIndependent K (fun n : ℕ ↦ (D : L → L)^[n] (u 0)) := by
  intro hAI
  let v : Fin (m + 2) → L := fun i ↦ (D : L → L)^[(i : ℕ)] (u 0)
  have hvLI : LinearIndependent K v :=
    (hAI.comp (fun i : Fin (m + 2) ↦ (i : ℕ)) Fin.val_injective).linearIndependent
  let S : Submodule K L := principalFiltration (K := K) u (m + 1)
  let W : Submodule K L := Submodule.span K (Set.range v)
  letI : Module.Finite K S := by
    dsimp [S, principalFiltration]
    exact FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hWS : W ≤ S := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact gradedPrincipalJet_mem_of_symbol_eq_zero
      D₀ D u symbol hcompat hstep m hm i
  have hfinrankWS : Module.finrank K W ≤ Module.finrank K S :=
    Submodule.finrank_mono hWS
  have hfinrankS : Module.finrank K S ≤ m + 1 := by
    dsimp [S, principalFiltration]
    simpa using (finrank_range_le_card (R := K)
      (fun j : Fin (m + 1) ↦ u j))
  have hcard : m + 2 = Module.finrank K W := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := K)).mp hvLI
    simpa [W, v] using h
  omega

/-- Exact graded principal-symbol horizon.  The complete cyclic jet is algebraically independent
if and only if every layer symbol is nonzero. -/
theorem gradedPrincipalJet_algebraicIndependent_iff
    (D₀ : Derivation k K K) (D : Derivation k L L) (u : ℕ → L)
    (symbol : ℕ → K)
    (hcompat : ∀ a : K, D (algebraMap K L a) = algebraMap K L (D₀ a))
    (hstep : ∀ n : ℕ,
      D (u n) - symbol n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u) :
    AlgebraicIndependent K (fun n : ℕ ↦ (D : L → L)^[n] (u 0)) ↔
      ∀ n, symbol n ≠ 0 := by
  constructor
  · intro hAI n hn
    exact not_algebraicIndependent_gradedPrincipalJet_of_symbol_eq_zero
      D₀ D u symbol hcompat hstep n hn hAI
  · intro hsymbol
    exact gradedPrincipalJet_algebraicIndependent
      D₀ D u symbol hcompat hstep hsymbol hu

/-- Each layer symbol is intrinsic to the filtered derivation action on an algebraically free
source sequence. -/
theorem gradedPrincipalSymbol_unique
    (D : Derivation k L L) (u : ℕ → L) (symbol₁ symbol₂ : ℕ → K)
    (hstep₁ : ∀ n : ℕ,
      D (u n) - symbol₁ n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1))
    (hstep₂ : ∀ n : ℕ,
      D (u n) - symbol₂ n • u (n + 1) ∈ principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u) :
    symbol₁ = symbol₂ := by
  funext n
  have hdiff : (symbol₂ n - symbol₁ n) • u (n + 1) ∈
      principalFiltration (K := K) u (n + 1) := by
    have h := (principalFiltration (K := K) u (n + 1)).sub_mem
      (hstep₁ n) (hstep₂ n)
    convert h using 1 <;> simp [sub_smul]
  have hsubset : Set.range (fun j : Fin (n + 1) ↦ u j) ⊆
      u '' (Set.univ \ {n + 1}) := by
    rintro y ⟨j, rfl⟩
    refine ⟨j, ?_, rfl⟩
    simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    exact Nat.ne_of_lt j.isLt
  have hspan : (symbol₂ n - symbol₁ n) • u (n + 1) ∈
      Submodule.span K (u '' (Set.univ \ {n + 1})) :=
    (Submodule.span_mono hsubset) hdiff
  have hzero := hu.linearIndependent.eq_zero_of_smul_mem_span
    (n + 1) (symbol₂ n - symbol₁ n) hspan
  exact (sub_eq_zero.mp hzero).symm

variable {g : Type*} [AddCommMonoid g] [Module k g]

/-- The non-hypertranscendental directions in a linear law space are exactly the union of the
kernels of all graded principal symbols. -/
theorem gradedPrincipalSymbolLawSpace_characteristicSet_eq_iUnion_ker
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u) :
    {A : g | ¬ AlgebraicIndependent K
      (fun n : ℕ ↦ ((law A : L → L)^[n] (u 0)))} =
      ⋃ n : ℕ, ((symbol n).ker : Set g) := by
  ext A
  have hiff := gradedPrincipalJet_algebraicIndependent_iff
    (coefficientLaw A) (law A) u (fun n ↦ symbol n A)
    (hcompat A) (hstep A) hu
  constructor
  · intro hnot
    have hvanish : ∃ n, symbol n A = 0 := by
      by_contra hall
      push Not at hall
      exact hnot (hiff.mpr hall)
    obtain ⟨n, hn⟩ := hvanish
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  · intro hmem hAI
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    have hnzero : symbol n A = 0 := hn
    exact (hiff.mp hAI n) hnzero

/-- The graded hypertranscendental law phase is the complement of the complete characteristic
arrangement. -/
theorem gradedPrincipalSymbolLawSpace_hypertranscendentalSet_eq_compl_iUnion_ker
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u) :
    {A : g | AlgebraicIndependent K
      (fun n : ℕ ↦ ((law A : L → L)^[n] (u 0)))} =
      (⋃ n : ℕ, ((symbol n).ker : Set g))ᶜ := by
  ext A
  have hiff := gradedPrincipalJet_algebraicIndependent_iff
    (coefficientLaw A) (law A) u (fun n ↦ symbol n A)
    (hcompat A) (hstep A) hu
  simpa using hiff

end

end GaloisForLFunctions.HTGeometry
