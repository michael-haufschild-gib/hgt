import GaloisForLFunctions.HeckeKreinToeplitz.TheMarginIsTheWidthOfTheIndexOneWindow

/-!
# The selective index of the atomic kernel is one square

At atomic resolution a sign gauge `ω` (`ω² = 1`) acts on the prime kernel by congruence, so every
twin has the index ladder of `ζ` (`hermNegIndex_gaugeAtom_eq`). The pole enters as one linear
condition, the pole hyperplane `Σ c_n n^{−1/2} = 0`. Its index is the **pole index**
(`poleNegIndex`): the largest dimension of a negative-definite subspace inside the hyperplane.

* **One condition costs at most one square** (`hermNegIndex_le_negIndexOn_ker_add_one`): the index
  on the kernel of a linear functional is at least the full index minus one.
* **Rigidity** (`poleNegIndex_gauge_le_add_one`): the pole indices of any two sign gauges differ by
  at most one, at every horizon and every counterterm.
* **Attained** (`eventually_poleNegIndex_window`): in the window `L − 2 log 2 < D < L`, `L = log N − γ`,
  the pole index of `ζ` is `0` and that of the Liouville twin is `1`.

So no count of negative squares at atomic resolution separates `ζ` from a sign twin by more than one:
an index ceiling `κ ≤ k` with `k ≥ 1` that holds for `ζ` at a horizon holds for every twin at that
horizon up to one square. The selective content of the atomic index is the single square that the
pole does or does not carry.
-/

open Complex Finset Filter Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory (PrimeHorizonIndex liouvilleSign
  liouvilleSign_mul_self)

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

local notation "γ" => Real.eulerMascheroniConstant

/-! ### The index on a subspace -/

section Restricted

variable {ι : Type*} [Fintype ι]

/-- The negative index of a Hermitian form on a subspace `V`: the largest dimension of a subspace of
`V` on which the form is negative definite. -/
def negIndexOn (H : Matrix ι ι ℂ) (V : Submodule ℂ (ι → ℂ)) : ℕ :=
  sSup {r | ∃ W : Submodule ℂ (ι → ℂ), W ≤ V ∧ Module.finrank ℂ W = r ∧ IsPosDefOn (-H) W}

theorem negIndexOn_bddAbove (H : Matrix ι ι ℂ) (V : Submodule ℂ (ι → ℂ)) :
    BddAbove {r | ∃ W : Submodule ℂ (ι → ℂ), W ≤ V ∧ Module.finrank ℂ W = r ∧
      IsPosDefOn (-H) W} := by
  refine ⟨Fintype.card ι, ?_⟩
  rintro r ⟨W, -, rfl, -⟩
  have h := Submodule.finrank_le W
  rwa [Module.finrank_fintype_fun_eq_card] at h

theorem finrank_le_negIndexOn {H : Matrix ι ι ℂ} {V W : Submodule ℂ (ι → ℂ)} (hWV : W ≤ V)
    (hW : IsPosDefOn (-H) W) : Module.finrank ℂ W ≤ negIndexOn H V :=
  le_csSup (negIndexOn_bddAbove H V) ⟨W, hWV, rfl, hW⟩

theorem exists_negIndexOn (H : Matrix ι ι ℂ) (V : Submodule ℂ (ι → ℂ)) :
    ∃ W : Submodule ℂ (ι → ℂ), W ≤ V ∧ Module.finrank ℂ W = negIndexOn H V ∧
      IsPosDefOn (-H) W :=
  Nat.sSup_mem (s := {r | ∃ W : Submodule ℂ (ι → ℂ), W ≤ V ∧ Module.finrank ℂ W = r ∧
      IsPosDefOn (-H) W})
    ⟨0, ⊥, bot_le, by simp, fun x hx hx0 => absurd (by simpa using hx) hx0⟩
    (negIndexOn_bddAbove H V)

/-- The index on a subspace is at most the full index. -/
theorem negIndexOn_le_hermNegIndex (H : Matrix ι ι ℂ) (V : Submodule ℂ (ι → ℂ)) :
    negIndexOn H V ≤ hermNegIndex H := by
  obtain ⟨W, -, hW, hneg⟩ := exists_negIndexOn H V
  rw [← hW]
  exact finrank_le_posIndex hneg

/-- **One linear condition costs at most one square.** -/
theorem hermNegIndex_le_negIndexOn_ker_add_one (H : Matrix ι ι ℂ) (φ : (ι → ℂ) →ₗ[ℂ] ℂ) :
    hermNegIndex H ≤ negIndexOn H (LinearMap.ker φ) + 1 := by
  obtain ⟨W, hrank, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-H)
  set ψ := φ.domRestrict W
  have hsum := LinearMap.finrank_range_add_finrank_ker ψ
  have hrange : Module.finrank ℂ (LinearMap.range ψ) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range ψ)
    rwa [Module.finrank_self] at this
  set V := (LinearMap.ker ψ).map W.subtype
  have hV : Module.finrank ℂ V = Module.finrank ℂ (LinearMap.ker ψ) :=
    LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ W.injective_subtype _).symm
  have hVker : V ≤ LinearMap.ker φ := by
    rintro y ⟨w, hw, rfl⟩
    exact hw
  have hneg : IsPosDefOn (-H) V := by
    rintro y ⟨w, -, rfl⟩ hy
    exact hW _ w.2 hy
  have h1 := finrank_le_negIndexOn hVker hneg
  rw [hV] at h1
  show hermPosIndex (-H) ≤ _
  rw [← hrank]
  omega

/-- A nonzero vector of `V` with negative form gives index at least one on `V`. -/
theorem one_le_negIndexOn {H : Matrix ι ι ℂ} {V : Submodule ℂ (ι → ℂ)} {c : ι → ℂ} (hcV : c ∈ V)
    (hc : hermQuad H c < 0) : 1 ≤ negIndexOn H V := by
  have hc0 : c ≠ 0 := by rintro rfl; simp [hermQuad] at hc
  have hspan : IsPosDefOn (-H) (Submodule.span ℂ {c}) := by
    intro x hx hx0
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ht : t ≠ 0 := by rintro rfl; exact hx0 (zero_smul _ _)
    have hq : hermQuad H (t • c) = Complex.normSq t * hermQuad H c := by
      simp only [hermQuad, Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, RCLike.star_def]
      rw [← mul_assoc, Complex.mul_conj, re_ofReal_mul]
    rw [hermQuad_neg, hq]
    nlinarith [Complex.normSq_pos.mpr ht]
  have h := finrank_le_negIndexOn ((Submodule.span_singleton_le_iff_mem c V).mpr hcV) hspan
  rwa [finrank_span_singleton hc0] at h

end Restricted

/-! ### The pole index of a sign gauge -/

/-- The **pole index**: the negative index of a form on the pole hyperplane. -/
def poleNegIndex (N : ℕ) (H : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℂ) : ℕ :=
  negIndexOn H (LinearMap.ker (poleFunctional N))

/-- The pole index of a sign gauge lies in `[κ − 1, κ]`, with `κ` the twin-blind index of `ζ`. -/
theorem poleNegIndex_gauge_bounds (N : ℕ) (D : ℝ) {ω : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1) :
    poleNegIndex N ((gaugeAtomMatrix N D ω).map (↑)) ≤
        hermNegIndex (gram (atomKernel D) (horizonPoint N)) ∧
      hermNegIndex (gram (atomKernel D) (horizonPoint N)) ≤
        poleNegIndex N ((gaugeAtomMatrix N D ω).map (↑)) + 1 := by
  rw [← hermNegIndex_gaugeAtom_eq N D hω]
  exact ⟨negIndexOn_le_hermNegIndex _ _, hermNegIndex_le_negIndexOn_ker_add_one _ _⟩

/-- **Rigidity.** The pole indices of two sign gauges differ by at most one. -/
theorem poleNegIndex_gauge_le_add_one (N : ℕ) (D : ℝ) {ω ω' : ℕ → ℝ} (hω : ∀ n, ω n * ω n = 1)
    (hω' : ∀ n, ω' n * ω' n = 1) :
    poleNegIndex N ((gaugeAtomMatrix N D ω).map (↑)) ≤
      poleNegIndex N ((gaugeAtomMatrix N D ω').map (↑)) + 1 :=
  (poleNegIndex_gauge_bounds N D hω).1.trans (poleNegIndex_gauge_bounds N D hω').2

/-- The trivial gauge is `ζ`. -/
theorem gaugeAtomMatrix_one (N : ℕ) (D : ℝ) :
    (gaugeAtomMatrix N D fun _ => 1).map (↑) = gram (atomKernel D) (horizonPoint N) := by
  rw [gram_atomKernel]
  ext m n
  simp [gaugeAtomMatrix]

/-- **Every sign twin is within one square of `ζ` on the pole hyperplane.** -/
theorem abs_poleNegIndex_gauge_sub_zeta_le_one (N : ℕ) (D : ℝ) {ω : ℕ → ℝ}
    (hω : ∀ n, ω n * ω n = 1) :
    poleNegIndex N ((gaugeAtomMatrix N D ω).map (↑)) ≤
        poleNegIndex N (gram (atomKernel D) (horizonPoint N)) + 1 ∧
      poleNegIndex N (gram (atomKernel D) (horizonPoint N)) ≤
        poleNegIndex N ((gaugeAtomMatrix N D ω).map (↑)) + 1 := by
  have h1 : ∀ n : ℕ, (fun _ : ℕ => (1 : ℝ)) n * (fun _ : ℕ => (1 : ℝ)) n = 1 := fun _ => by norm_num
  rw [← gaugeAtomMatrix_one]
  exact ⟨poleNegIndex_gauge_le_add_one N D hω h1, poleNegIndex_gauge_le_add_one N D h1 hω⟩

/-- **The one square is attained.** In the index-one window the pole index of `ζ` is `0` and that of
the Liouville twin is `1`. -/
theorem eventually_poleNegIndex_window {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ D : ℝ, Real.log N - γ - 2 * Real.log 2 + ε ≤ D → D < Real.log N - γ - ε →
      poleNegIndex N (gram (atomKernel D) (horizonPoint N)) = 0 ∧
        poleNegIndex N ((gaugeAtomMatrix N D liouvilleSign).map (↑)) = 1 := by
  filter_upwards [eventually_hermQuad_atom_nonneg_on_pole hε,
    eventually_exists_neg_on_pole_liouville hε, eventually_hermNegIndex_atom_le_one hε]
    with N hpole hliou hle D hD₁ hD₂
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · obtain ⟨W, hWV, hW, hneg⟩ := exists_negIndexOn (gram (atomKernel D) (horizonPoint N))
      (LinearMap.ker (poleFunctional N))
    rw [poleNegIndex, ← hW, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have h1 := hneg x hx hx0
    have h2 := hpole D hD₁ x (LinearMap.mem_ker.mp (hWV hx))
    rw [hermQuad_neg] at h1
    linarith
  · exact (poleNegIndex_gauge_bounds N D liouvilleSign_mul_self).1.trans (hle D hD₁)
  · obtain ⟨c, hc0, hc⟩ := hliou D hD₂
    exact one_le_negIndexOn (LinearMap.mem_ker.mpr hc0) hc

end GaloisForLFunctions.HeckeKreinToeplitz
