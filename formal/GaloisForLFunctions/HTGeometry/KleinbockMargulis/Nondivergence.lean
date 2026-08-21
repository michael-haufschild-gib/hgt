import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LatticeFinite
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Marked
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.Setup
import Mathlib.Topology.Order.Lattice
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Quantitative non-divergence in the space of lattices (Kleinbock–Margulis, Theorem 5.2)

The poset of §5 is the set of nonzero rational subspaces of `ℚ^k`, ordered by inclusion; its
length is `k` because along a chain the dimension strictly increases.  To a subspace `W` and a
point `x` one attaches `ψ_W(x) = ‖h(x)(W ∩ ℤ^k)‖`.  Conditions (A1)–(A3) of §4 are the hypotheses
(i), (ii) of the theorem together with the finiteness proved in `finite_latticeWedgeNorm_lt`, so
Theorem 4.1 applies.

The remaining point is that a marked point cannot carry a short lattice vector.  Given `v ≠ 0`,
let `Wm` be the largest element of the marking chain (together with `{0}`) not containing `v`, and
`Λ = Wm + ℚv`.  Then `Λ` is comparable with the whole chain, so `‖h(x)Λ‖ ≥ ε`, while
`‖h(x)Γ_{Wm}‖ ≤ ρ` — or `Wm = {0}`, where the norm is `1` and Lemma 5.1 has constant `1`.  In
both cases Lemma 5.1 gives `‖h(x)v‖ ≥ ε`.

## Main results

* `lengthLE_nonzero_subspaces` — the poset has length `k`.
* `theorem_5_2` — quantitative non-divergence.
-/

open Matrix Finset Module Set MeasureTheory Metric
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HTGeometry.KleinbockMargulis

variable {d k : ℕ}

/-! ### Continuity of the lattice norm -/

theorem continuousOn_finsetSup' {X ι : Type*} [TopologicalSpace X] {s : Set X} {t : Finset ι}
    (ht : t.Nonempty) {f : ι → X → ℝ} (hf : ∀ i ∈ t, ContinuousOn (f i) s) :
    ContinuousOn (fun x => t.sup' ht fun i => f i x) s := by
  induction ht using Finset.Nonempty.cons_induction with
  | singleton i =>
      simp only [Finset.sup'_singleton]
      exact hf i (by simp)
  | cons i t hi ht ih =>
      have hrw : (fun x => (Finset.cons i t hi).sup' (Finset.cons_nonempty hi) fun j => f j x)
          = fun x => f i x ⊔ t.sup' ht fun j => f j x := by
        funext x
        exact Finset.sup'_cons (f := fun j => f j x) (H := ht)
      rw [hrw]
      exact ContinuousOn.sup' (hf i (by simp)) (ih fun j hj => hf j (by simp [hj]))

theorem wedgeNorm_eq_sup' {j : ℕ} [Nonempty (Fin j → Fin k)] (V : Fin j → (Fin k → ℝ)) :
    wedgeNorm V = Finset.univ.sup' Finset.univ_nonempty fun σ => |plucker V σ| :=
  (Finset.sup'_univ_eq_ciSup _).symm

/-- If a tuple of length `0` is given, its wedge norm is `1`. -/
theorem wedgeNorm_of_length_zero {j : ℕ} (hj : j = 0) (V : Fin j → (Fin k → ℝ)) :
    wedgeNorm V = 1 := by
  subst hj
  exact wedgeNorm_zero V

theorem continuousOn_latticeWedgeNorm (hk : 0 < k) (W : Submodule ℚ (Fin k → ℚ))
    {X : Type*} [TopologicalSpace X] {s : Set X} {h : X → Matrix (Fin k) (Fin k) ℝ}
    (hcont : ∀ i c, ContinuousOn (fun x => h x i c) s) :
    ContinuousOn (fun x => latticeWedgeNorm (h x) W) s := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  have hentry : ∀ (a : Fin (latticeRank W)) (i : Fin k),
      ContinuousOn (fun x => ((h x).mulVec (intToReal (latticeBasis W a))) i) s := by
    intro a i
    simp only [Matrix.mulVec, dotProduct]
    exact continuousOn_finsetSum _ fun c _ => (hcont i c).mul continuousOn_const
  have hplucker : ∀ σ : Fin (latticeRank W) → Fin k,
      ContinuousOn (fun x => |plucker (fun a => (h x).mulVec (intToReal (latticeBasis W a))) σ|) s := by
    intro σ
    refine ContinuousOn.abs ?_
    simp only [plucker, Matrix.det_apply']
    refine continuousOn_finsetSum _ fun π _ => ?_
    refine ContinuousOn.mul continuousOn_const ?_
    exact continuousOn_finsetProd _ fun a _ => hentry _ _
  have hrw : (fun x => latticeWedgeNorm (h x) W)
      = fun x => Finset.univ.sup' Finset.univ_nonempty
          fun σ => |plucker (fun a => (h x).mulVec (intToReal (latticeBasis W a))) σ| := by
    funext x
    exact wedgeNorm_eq_sup' _
  rw [hrw]
  exact continuousOn_finsetSup' _ fun σ _ => hplucker σ

/-! ### The poset of nonzero rational subspaces -/

theorem lengthLE_nonzero_subspaces (k : ℕ) :
    LengthLE {W : Submodule ℚ (Fin k → ℚ) | W ≠ ⊥} k := by
  classical
  intro c hc hchain
  have hinj : Set.InjOn (fun W : Submodule ℚ (Fin k → ℚ) => Module.finrank ℚ W) ↑c := by
    intro W hW W' hW' heq
    by_contra hne
    rcases hchain hW hW' hne with hle | hle
    · exact absurd heq (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)).ne
    · exact absurd heq.symm
        (Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle (Ne.symm hne))).ne
  have himg : c.image (fun W : Submodule ℚ (Fin k → ℚ) => Module.finrank ℚ W) ⊆ Finset.Icc 1 k := by
    intro n hn
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hn
    have hne : W ≠ ⊥ := hc hW
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · refine Nat.one_le_iff_ne_zero.mpr fun hzero => hne ?_
      exact Submodule.finrank_eq_zero.mp hzero
    · have h1 : Module.finrank ℚ W ≤ Module.finrank ℚ (Fin k → ℚ) := Submodule.finrank_le W
      simpa [Module.finrank_fin_fun] using h1
  calc c.card
      = (c.image fun W : Submodule ℚ (Fin k → ℚ) => Module.finrank ℚ W).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 k).card := Finset.card_le_card himg
    _ = k := by simp


theorem latticeWedgeNorm_nonneg [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    (W : Submodule ℚ (Fin k → ℚ)) : 0 ≤ latticeWedgeNorm A W := wedgeNorm_nonneg _

theorem abs_latticeWedgeNorm [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ)
    (W : Submodule ℚ (Fin k → ℚ)) : |latticeWedgeNorm A W| = latticeWedgeNorm A W :=
  abs_of_nonneg (latticeWedgeNorm_nonneg A W)

/-! ### Theorem 5.2 -/

/-- **Theorem 5.2.**  If every `ψ_W(x) = ‖h(x)(W ∩ ℤ^k)‖` is `(C, α)`-good on `B̃` and has
supremum norm at least `ρ ≤ 1/k` on `B`, then for `0 < ε ≤ ρ`

`|{x ∈ B : δ(h(x)ℤ^k) < ε}| ≤ k C (3^d N_d)^k (ε/ρ)^α |B|`. -/
theorem theorem_5_2 (hk : 0 < k) {C α ρ : ℝ} (hC : 0 < C) (hα : 0 < α) (hρ : 0 < ρ)
    (hρk : (k : ℝ) * ρ ≤ 1) {x₀ : Fin d → ℝ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    {h : (Fin d → ℝ) → Matrix (Fin k) (Fin k) ℝ}
    (hcont : ∀ i c, ContinuousOn (fun x => h x i c) (ball x₀ (3 ^ k * r₀)))
    (hinv : ∀ x ∈ ball x₀ (3 ^ k * r₀), IsUnit (h x).det)
    (hgood : ∀ W : Submodule ℚ (Fin k → ℚ), W ≠ ⊥ →
      IsGood C α (fun x => latticeWedgeNorm (h x) W) (ball x₀ (3 ^ k * r₀)))
    (hsupB : ∀ W : Submodule ℚ (Fin k → ℚ), W ≠ ⊥ →
      SupGe (fun x => latticeWedgeNorm (h x) W) (ball x₀ r₀) ρ)
    {ε : ℝ} (hε : 0 < ε) (hερ : ε ≤ ρ) :
    volume {x ∈ ball x₀ r₀ | latticeDelta (h x) < ε}
      ≤ ENNReal.ofReal ((k : ℝ) * C
          * ((3 : ℝ) ^ d * (Besicovitch.multiplicity (Fin d → ℝ) : ℝ)) ^ k * (ε / ρ) ^ α)
        * volume (ball x₀ r₀) := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  set S : Set (Submodule ℚ (Fin k → ℚ)) := {W | W ≠ ⊥} with hSdef
  set ψ : Submodule ℚ (Fin k → ℚ) → (Fin d → ℝ) → ℝ :=
    fun W x => latticeWedgeNorm (h x) W with hψdef
  -- (5.2): a marked point carries no short lattice vector
  have hmark : ∀ z ∈ ball x₀ r₀, IsMarked ε ρ S ψ z → ε ≤ latticeDelta (h z) := by
    intro z _ hmarked
    obtain ⟨T, hTS, hTchain, hM1, hM2⟩ := hmarked
    refine le_latticeDelta hk fun v hv => ?_
    show ε ≤ ‖(h z).mulVec (intToReal v)‖
    have hvQ : intToRat v ≠ 0 := by
      intro hcon
      refine hv (intToRat_injective ?_)
      rw [hcon]
      funext i
      simp [intToRat]
    -- the elements of the chain, together with `{0}`, that do not contain `v`
    have hTfin : T.Finite := by
      by_contra hinf
      rw [Set.not_finite] at hinf
      obtain ⟨c, hcT, hccard⟩ := hinf.exists_subset_card_eq (k + 1)
      have hle := lengthLE_nonzero_subspaces k c (fun W hW => hTS (hcT hW)) (hTchain.mono hcT)
      omega
    set P : Set (Submodule ℚ (Fin k → ℚ)) := {W | W ∈ insert ⊥ T ∧ intToRat v ∉ W} with hPdef
    have hPne : P.Nonempty := by
      refine ⟨⊥, Or.inl rfl, ?_⟩
      simpa using hvQ
    have hPfin : P.Finite := (hTfin.insert ⊥).subset fun W hW => hW.1
    obtain ⟨Wm, hWmP, hWmmax⟩ :=
      Set.exists_max_image P (fun W => Module.finrank ℚ W) hPfin hPne
    have hcompP : ∀ W ∈ insert ⊥ T, ∀ W' ∈ insert ⊥ T, W ≤ W' ∨ W' ≤ W := by
      intro W hW W' hW'
      rcases hW with rfl | hW
      · exact Or.inl bot_le
      rcases hW' with rfl | hW'
      · exact Or.inr bot_le
      by_cases heq : W = W'
      · exact Or.inl (le_of_eq heq)
      · exact hTchain hW hW' heq
    have hWmle : ∀ W ∈ P, W ≤ Wm := by
      intro W hW
      rcases hcompP W hW.1 Wm hWmP.1 with h1 | h1
      · exact h1
      · by_cases heq : Wm = W
        · exact le_of_eq heq.symm
        · have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne h1 heq)
          have := hWmmax W hW
          omega
    -- the subspace spanned by `Wm` and `v`
    set Λ : Submodule ℚ (Fin k → ℚ) := Wm ⊔ Submodule.span ℚ {intToRat v} with hΛdef
    have hvΛ : intToRat v ∈ Λ := by
      have hle : Submodule.span ℚ {intToRat v} ≤ Λ := le_sup_right
      exact hle (Submodule.mem_span_singleton_self (intToRat v))
    have hvWm : intToRat v ∉ Wm := hWmP.2
    have hWmΛ : Wm ≤ Λ := le_sup_left
    have hΛne : Λ ≠ ⊥ := by
      intro hb
      rw [hb, Submodule.mem_bot] at hvΛ
      exact hvQ hvΛ
    have hinf : Wm ⊓ Submodule.span ℚ {intToRat v} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro y ⟨hyW, hyS⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyS
      by_cases hc : c = 0
      · simp [hc]
      · refine absurd ?_ hvWm
        have hrw : intToRat v = c⁻¹ • (c • intToRat v) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        rw [hrw]
        exact Wm.smul_mem _ hyW
    have hdim : Module.finrank ℚ Λ = Module.finrank ℚ Wm + 1 := by
      have hkey := Submodule.finrank_sup_add_finrank_inf_eq Wm (Submodule.span ℚ {intToRat v})
      rw [hinf, finrank_span_singleton hvQ] at hkey
      simpa [hΛdef] using hkey
    have hrankΛ : latticeRank Λ = latticeRank Wm + 1 := by
      rw [latticeRank_eq_finrank, latticeRank_eq_finrank, hdim]
    -- `Λ` is comparable with the whole chain
    have hΛcomp : ∀ W ∈ T, W ≤ Λ ∨ Λ ≤ W := by
      intro W hW
      by_cases hvin : intToRat v ∈ W
      · refine Or.inr (sup_le ?_ ?_)
        · rcases hcompP Wm hWmP.1 W (Or.inr hW) with h1 | h1
          · exact h1
          · exact absurd (h1 hvin) hvWm
        · exact Submodule.span_le.mpr (by simpa using hvin)
      · exact Or.inl (le_trans (hWmle W ⟨Or.inr hW, hvin⟩) hWmΛ)
    -- the marking gives `ψ_Λ(z) ≥ ε`
    have hΛε : ε ≤ latticeWedgeNorm (h z) Λ := by
      by_cases hΛT : Λ ∈ T
      · have hb := (hM1 Λ hΛT).1
        simpa only [hψdef, abs_latticeWedgeNorm] using hb
      · have hΛsub : Λ ∈ subPoset S T :=
          ⟨hΛne, hΛT, fun t ht => (hΛcomp t ht).symm⟩
        have hb := hM2 Λ hΛsub
        simp only [hψdef, abs_latticeWedgeNorm] at hb
        linarith
    -- Lemma 5.1
    have hL51 := lemma_5_1 (h z) hWmΛ (W := Wm) (W' := Λ) (by simpa using hvΛ) hvWm hdim
    have hnn : 0 ≤ ‖(h z).mulVec (intToReal v)‖ := norm_nonneg _
    rcases hWmP.1 with hbot | hWmT
    · -- `Wm = {0}`: the constant of Lemma 5.1 is `1` and `‖h(z){0}‖ = 1`
      have hr0 : latticeRank Wm = 0 := by
        rw [latticeRank_eq_finrank, hbot]
        simp
      have hone : latticeWedgeNorm (h z) Wm = 1 :=
        wedgeNorm_of_length_zero hr0 _
      rw [hr0, hone] at hL51
      push_cast at hL51
      have : latticeWedgeNorm (h z) Λ ≤ ‖(h z).mulVec (intToReal v)‖ := by linarith
      exact le_trans hΛε this
    · -- `Wm` belongs to the chain, so `‖h(z)Γ_{Wm}‖ ≤ ρ`
      have hρbound : latticeWedgeNorm (h z) Wm ≤ ρ := by
        have hb := (hM1 Wm hWmT).2
        simpa only [hψdef, abs_latticeWedgeNorm] using hb
      have hrle : ((latticeRank Wm : ℝ) + 1) ≤ (k : ℝ) := by
        have h1 : latticeRank Λ ≤ k := latticeRank_le Λ
        rw [hrankΛ] at h1
        exact_mod_cast h1
      have hwnn : 0 ≤ latticeWedgeNorm (h z) Wm := wedgeNorm_nonneg _
      have hstep : latticeWedgeNorm (h z) Λ
          ≤ (k : ℝ) * ρ * ‖(h z).mulVec (intToReal v)‖ := by
        refine hL51.trans ?_
        have h2 : ((latticeRank Wm : ℝ) + 1) * latticeWedgeNorm (h z) Wm ≤ (k : ℝ) * ρ := by
          nlinarith
        exact mul_le_mul_of_nonneg_right h2 hnn
      have hfin : (k : ℝ) * ρ * ‖(h z).mulVec (intToReal v)‖
          ≤ ‖(h z).mulVec (intToReal v)‖ := by
        nlinarith
      linarith
  -- assemble with Theorem 4.1
  have hsub : {x ∈ ball x₀ r₀ | latticeDelta (h x) < ε}
      ⊆ {z ∈ ball x₀ r₀ | ¬ IsMarked ε ρ S ψ z} := by
    rintro x ⟨hx, hlt⟩
    exact ⟨hx, fun hm => absurd (hmark x hx hm) (not_le.mpr hlt)⟩
  refine le_trans (measure_mono hsub) ?_
  refine measure_not_marked_le hC hα hρ k S ψ x₀ r₀ hr₀ (lengthLE_nonzero_subspaces k)
    (fun W hW => continuousOn_latticeWedgeNorm hk W hcont)
    (fun W hW => hgood W hW) (fun W hW => hsupB W hW) ?_ ε hε
  intro x hx
  refine (finite_latticeWedgeNorm_lt hk (hinv x hx) ρ).subset ?_
  rintro W ⟨-, hW⟩
  show latticeWedgeNorm (h x) W < ρ
  simpa only [hψdef, abs_latticeWedgeNorm] using hW

end GaloisForLFunctions.HTGeometry.KleinbockMargulis
