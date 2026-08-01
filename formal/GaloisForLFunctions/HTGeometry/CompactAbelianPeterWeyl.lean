import GaloisForLFunctions.HTGeometry.CompactAbelianInvariantSplit

/-!
# Peter–Weyl for compact abelian groups: characters separate points

Suppose every continuous character of `G` is trivial at `g`.  Then translation by `g` is the
identity on every eigenspace of every Hermitian convolution operator with nonzero eigenvalue, hence
on the kernel `N` of `T g - 1`.  A vector orthogonal to `N` is orthogonal to all those eigenspaces,
so its image under every Hermitian convolution operator is orthogonal to *all* eigenspaces, hence
zero by the spectral theorem; and a vector annihilated by every Hermitian convolution is zero.  So
`N` is everything, translation by `g` is the identity, and Urysohn's lemma forces `g = 0`.

Therefore the continuous characters of a compact abelian group separate its points.
-/

open MeasureTheory TopologicalSpace

namespace GaloisForLFunctions

namespace CompactAbelian

noncomputable section

variable {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]

omit [T2Space G] in
/-- If every continuous character is trivial at `g`, then translation by `g` is the identity. -/
theorem transOp_eq_self_of_all_characters_trivial {g : G}
    (hchar : ∀ χ : G → ℂ, Continuous χ → (∀ a b, χ (a + b) = χ a * χ b) →
      (∀ a, ‖χ a‖ = 1) → χ g = 1) (v : Lp ℂ 2 (haarProb G)) :
    transOp g v = v := by
  classical
  set D : Lp ℂ 2 (haarProb G) →L[ℂ] Lp ℂ 2 (haarProb G) :=
    transOp g - ContinuousLinearMap.id ℂ (Lp ℂ 2 (haarProb G)) with hD
  set N : Submodule ℂ (Lp ℂ 2 (haarProb G)) := LinearMap.ker D.toLinearMap with hN
  have hmemN : ∀ u : Lp ℂ 2 (haarProb G), u ∈ N ↔ transOp g u = u := by
    intro u
    rw [hN, LinearMap.mem_ker]
    constructor
    · intro h
      have : transOp g u - u = 0 := h
      linear_combination (norm := module) this
    · intro h
      show transOp g u - u = 0
      rw [h, sub_self]
  have hNclosed : IsClosed (N : Set (Lp ℂ 2 (haarProb G))) := by
    rw [hN]
    exact ContinuousLinearMap.isClosed_ker D
  haveI : CompleteSpace N := hNclosed.completeSpace_coe
  -- a vector orthogonal to `N` vanishes
  have hperp : ∀ v ∈ Nᗮ, v = (0 : Lp ℂ 2 (haarProb G)) := by
    intro v hv
    refine eq_zero_of_inner_hermitian fun f hf => ?_
    set k : G → ℂ := fun z => f z with hk'
    have hk : Continuous k := f.continuous
    have hC : ∀ z, ‖k z‖ ≤ ‖f‖ := fun z => f.norm_coe_le_norm z
    have hsymm : LinearMap.IsSymmetric (convOp k hk hC).toLinearMap :=
      isSymmetric_convOp k hk hC hf
    have hcomp : IsCompactOperator (convOp k hk hC) := isCompactOperator_convOp k hk hC
    -- eigenspaces with nonzero eigenvalue consist of fixed vectors of `T g`
    have heig : ∀ μ : ℂ, μ ≠ 0 →
        ∀ u ∈ Module.End.eigenspace (convOp k hk hC).toLinearMap μ, transOp g u = u := by
      intro μ hμ
      haveI := ContinuousLinearMap.finite_dimensional_eigenspace hcomp μ hμ
      have hinv : ∀ a : G, ∀ u ∈ Module.End.eigenspace (convOp k hk hC).toLinearMap μ,
          transOp a u ∈ Module.End.eigenspace (convOp k hk hC).toLinearMap μ := by
        intro a u hu
        rw [Module.End.mem_eigenspace_iff] at hu ⊢
        have hu' : convOp k hk hC u = μ • u := hu
        show convOp k hk hC (transOp a u) = μ • transOp a u
        rw [convOp_transOp k hk hC a u]
        show transOp a (convOp k hk hC u) = μ • transOp a u
        rw [hu', map_smul]
      have heigen : ∀ u ∈ Module.End.eigenspace (convOp k hk hC).toLinearMap μ,
          convOp k hk hC u = μ • u := by
        intro u hu
        rw [Module.End.mem_eigenspace_iff] at hu
        exact hu
      exact transOp_eq_self_of_finite_invariant k hk hC hμ hchar
        (Module.finrank ℂ (Module.End.eigenspace (convOp k hk hC).toLinearMap μ))
        _ inferInstance rfl hinv heigen
    -- hence `T v` is orthogonal to every eigenspace
    have hTv : convOp k hk hC v = 0 := by
      have hmem : convOp k hk hC v ∈
          (⨆ μ : ℂ, Module.End.eigenspace (convOp k hk hC).toLinearMap μ)ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro y hy
        refine Submodule.iSup_induction
          (motive := fun z => inner ℂ z (convOp k hk hC v) = (0 : ℂ)) _ hy ?_ ?_ ?_
        · intro μ u hu
          have hsym := hsymm u v
          have huv : inner ℂ u (convOp k hk hC v) = inner ℂ (convOp k hk hC u) v := hsym.symm
          rw [huv]
          have hue : convOp k hk hC u = μ • u := by
            rw [Module.End.mem_eigenspace_iff] at hu
            exact hu
          rw [hue, inner_smul_left]
          rcases eq_or_ne μ 0 with hμ | hμ
          · rw [hμ]
            simp
          · have huN : u ∈ N := (hmemN u).mpr (heig μ hμ u hu)
            have hzero : inner ℂ u v = (0 : ℂ) := (Submodule.mem_orthogonal N v).mp hv u huN
            rw [hzero, mul_zero]
        · simp
        · intro x y hx hy2
          rw [inner_add_left, hx, hy2, add_zero]
      have hbot := ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hcomp hsymm
      rw [hbot, Submodule.mem_bot] at hmem
      exact hmem
    have hfeq : (⟨k, hk⟩ : C(G, ℂ)) = f := rfl
    have := inner_toLp_eq_zero_of_convOp_eq_zero k hk hC hf hTv
    rwa [hfeq] at this
  have hNtop : N = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    exact hperp x hx
  exact (hmemN v).mp (by rw [hNtop]; trivial)

/-- **Peter–Weyl for compact abelian groups: the continuous characters separate points.** -/
theorem exists_character_ne_one {g : G} (hg : g ≠ 0) :
    ∃ χ : G → ℂ, Continuous χ ∧ (∀ a b, χ (a + b) = χ a * χ b) ∧ (∀ a, ‖χ a‖ = 1) ∧ χ g ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hchar : ∀ χ : G → ℂ, Continuous χ → (∀ a b, χ (a + b) = χ a * χ b) →
      (∀ a, ‖χ a‖ = 1) → χ g = 1 := fun χ h1 h2 h3 => hcon χ h1 h2 h3
  -- Urysohn separates `0` from `g`
  obtain ⟨φ, hφ0, hφg, -⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_singleton (x := (0 : G)))
      (isClosed_singleton (x := g)) (by
        simpa [Set.disjoint_singleton] using fun h => hg h.symm)
  set ψ : C(G, ℂ) := ⟨fun x => (φ x : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩ with hψ
  have hfix := transOp_eq_self_of_all_characters_trivial hchar
    (ContinuousMap.toLp 2 (haarProb G) ℂ ψ)
  -- the fixed-point relation, pointwise for the continuous representative
  have hae : (fun x : G => ψ (x + g)) =ᵐ[haarProb G] fun x : G => ψ x := by
    have h1 := transOp_coeFn g (ContinuousMap.toLp 2 (haarProb G) ℂ ψ)
    have h2 : (fun x : G =>
        ((transOp g (ContinuousMap.toLp 2 (haarProb G) ℂ ψ) : Lp ℂ 2 (haarProb G)) : G → ℂ) x)
        =ᵐ[haarProb G] fun x : G =>
          ((ContinuousMap.toLp 2 (haarProb G) ℂ ψ : Lp ℂ 2 (haarProb G)) : G → ℂ) x := by
      rw [hfix]
    have h3 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (haarProb G) ψ
    have h4 := (measurePreserving_translate (G := G) g).quasiMeasurePreserving.ae_eq_comp h3
    filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
    simp only [Function.comp_apply] at hx4
    rw [← hx4, ← hx1, hx2, hx3]
  have hcont1 : Continuous fun x : G => ψ (x + g) :=
    ψ.continuous.comp (continuous_id.add continuous_const)
  have heq : (fun x : G => ψ (x + g)) = fun x : G => ψ x :=
    (hcont1.ae_eq_iff_eq (haarProb G) ψ.continuous).mp hae
  have h0 : ψ (0 + g) = ψ 0 := congrFun heq 0
  rw [zero_add] at h0
  have hg1 : φ g = 1 := hφg rfl
  have h00 : φ 0 = 0 := hφ0 rfl
  rw [hψ] at h0
  have : (1 : ℂ) = 0 := by
    have hgg : ((φ g : ℝ) : ℂ) = ((φ 0 : ℝ) : ℂ) := h0
    rw [hg1, h00] at hgg
    exact_mod_cast hgg
  exact one_ne_zero this

end

end CompactAbelian

end GaloisForLFunctions
