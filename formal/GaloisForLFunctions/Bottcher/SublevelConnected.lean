/-
# Connectedness of the filled-Julia sublevel sets `C_n = (escapeLevel c n)ᶜ`

The escape filtration `escapeLevel c n = {z | fⁿ z escapes}` is *increasing*; its complements
`C_n = {z | ‖fⁿ z‖ ≤ R}` are the **sublevel sets** of the escape-time, a *decreasing* nest of
compact sets whose intersection is the filled Julia set `K_c` (`compl_filledJulia_eq_iUnion_level`).

This file proves each `C_n` is preconnected, for a parameter whose critical value never escapes
(`hc : ∀ n, c ∉ escapeLevel c n`, i.e. `c ∈ mandelbrot`). The engine is a purely topological fact
about the squaring map — `isPreconnected_sq_preimage` — combined with the recursion
`C_{n+1} = f_c⁻¹(C_n) = {z | z² ∈ (C_n − c)}`, where `0 ∈ C_n − c` is exactly `c ∈ C_n = hc n`.

Downstream (`FilledJuliaConnected`) this nest + a nested-intersection-of-connected-compacts theorem
yields `IsPreconnected (filledJulia c)`, the `hconn` hypothesis consumed across `JuliaFrontierPerfect`
and `RelativeRigidityCapstone`.
-/
import GaloisForLFunctions.Bottcher.BasinConnected

open Topology

/-- **`z ↦ z²` sends connected sets containing `0` to connected preimages.** If `T ⊆ ℂ` is
preconnected and `0 ∈ T`, then `{z | z² ∈ T}` is preconnected. The two square-root sheets are glued
only at `0`; the deck involution `z ↦ -z` fixes `0`, and a separation of the preimage would descend —
through the open map `z ↦ z²` and the fiber-saturated pieces `U∩(−U)`, `V∩(−V)`, `(U∩−V)∪(V∩−U)` — to
a separation of `T`, contradicting `IsPreconnected T`. -/
theorem isPreconnected_sq_preimage {T : Set ℂ} (hT : IsPreconnected T) (h0 : (0 : ℂ) ∈ T) :
    IsPreconnected {z : ℂ | z ^ (2 : ℕ) ∈ T} := by
  have hsqopen : IsOpenMap (fun z : ℂ => z ^ (2 : ℕ)) := (Complex.isOpenQuotientMap_pow 2).isOpenMap
  have hsqsurj : Function.Surjective (fun z : ℂ => z ^ (2 : ℕ)) :=
    (Complex.isOpenQuotientMap_pow 2).surjective
  set A : Set ℂ := {z | z ^ (2 : ℕ) ∈ T} with hAdef
  have hmemA : ∀ {z : ℂ}, z ∈ A ↔ z ^ (2 : ℕ) ∈ T := fun {z} => Iff.rfl
  have hnegA : ∀ {z : ℂ}, z ∈ A → -z ∈ A := by
    intro z hz; rw [hmemA] at hz ⊢; simpa [neg_pow] using hz
  have himg : ∀ w : Set ℂ,
      (fun z : ℂ => z ^ (2 : ℕ)) '' (A ∩ w) = T ∩ (fun z : ℂ => z ^ (2 : ℕ)) '' w := by
    intro w; ext y; constructor
    · rintro ⟨z, ⟨hzA, hzw⟩, rfl⟩; exact ⟨hzA, z, hzw, rfl⟩
    · rintro ⟨hyT, z, hzw, rfl⟩; exact ⟨z, ⟨hyT, hzw⟩, rfl⟩
  have hkey : ∀ z₁ z₂ : ℂ, z₁ ^ (2 : ℕ) = z₂ ^ (2 : ℕ) → z₂ = z₁ ∨ z₂ = -z₁ := by
    intro z₁ z₂ h
    have hfac : (z₂ - z₁) * (z₂ + z₁) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inl (by linear_combination h')
    · exact Or.inr (by linear_combination h')
  intro u v hu hv hAuv hAu hAv
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hnouv : ∀ z, z ∈ A → z ∈ u → z ∈ v → False := fun z hz hzu hzv =>
    (Set.eq_empty_iff_forall_notMem.mp hcon z) ⟨hz, hzu, hzv⟩
  have hnu : IsOpen (Neg.neg ⁻¹' u : Set ℂ) := hu.preimage continuous_neg
  have hnv : IsOpen (Neg.neg ⁻¹' v : Set ℂ) := hv.preimage continuous_neg
  set OU : Set ℂ := (fun z : ℂ => z ^ (2 : ℕ)) '' (u ∩ Neg.neg ⁻¹' u) with hOUdef
  set OV : Set ℂ := (fun z : ℂ => z ^ (2 : ℕ)) '' (v ∩ Neg.neg ⁻¹' v) with hOVdef
  set OM : Set ℂ :=
    (fun z : ℂ => z ^ (2 : ℕ)) '' ((u ∩ Neg.neg ⁻¹' v) ∪ (v ∩ Neg.neg ⁻¹' u)) with hOMdef
  have hOU : IsOpen OU := hsqopen _ (hu.inter hnu)
  have hOV : IsOpen OV := hsqopen _ (hv.inter hnv)
  have hOM : IsOpen OM := hsqopen _ ((hu.inter hnv).union (hv.inter hnu))
  have hTU : T ∩ OU = (fun z : ℂ => z ^ (2 : ℕ)) '' (A ∩ (u ∩ Neg.neg ⁻¹' u)) := (himg _).symm
  have hTV : T ∩ OV = (fun z : ℂ => z ^ (2 : ℕ)) '' (A ∩ (v ∩ Neg.neg ⁻¹' v)) := (himg _).symm
  have hTM : T ∩ OM =
      (fun z : ℂ => z ^ (2 : ℕ)) '' (A ∩ ((u ∩ Neg.neg ⁻¹' v) ∪ (v ∩ Neg.neg ⁻¹' u))) := (himg _).symm
  have hcover : T ⊆ OU ∪ (OV ∪ OM) := by
    intro w hwT
    obtain ⟨z, hz⟩ := hsqsurj w
    have hzsq : z ^ (2 : ℕ) = w := hz
    have hzA : z ∈ A := by rw [hmemA, hzsq]; exact hwT
    have hnzA : -z ∈ A := hnegA hzA
    rcases hAuv hzA with hzu | hzv
    · rcases hAuv hnzA with hnzu | hnzv
      · exact Or.inl ⟨z, ⟨hzu, hnzu⟩, hzsq⟩
      · exact Or.inr (Or.inr ⟨z, Or.inl ⟨hzu, hnzv⟩, hzsq⟩)
    · rcases hAuv hnzA with hnzu | hnzv
      · exact Or.inr (Or.inr ⟨z, Or.inr ⟨hzv, hnzu⟩, hzsq⟩)
      · exact Or.inr (Or.inl ⟨z, ⟨hzv, hnzv⟩, hzsq⟩)
  have hdisjUV : (T ∩ OU) ∩ (T ∩ OV) = ∅ := by
    rw [hTU, hTV, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨z₁, ⟨hz₁A, hz₁u, hz₁nu⟩, rfl⟩, ⟨z₂, ⟨hz₂A, hz₂v, hz₂nv⟩, hz₂eq⟩⟩
    rcases hkey z₁ z₂ hz₂eq.symm with h | h
    · subst z₂; exact hnouv z₁ hz₁A hz₁u hz₂v
    · subst z₂; exact hnouv (-z₁) (hnegA hz₁A) hz₁nu hz₂v
  have hdisjUM : (T ∩ OU) ∩ (T ∩ OM) = ∅ := by
    rw [hTU, hTM, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨z₁, ⟨hz₁A, hz₁u, hz₁nu⟩, rfl⟩, ⟨z₂, ⟨hz₂A, hz₂m⟩, hz₂eq⟩⟩
    rcases hkey z₁ z₂ hz₂eq.symm with h | h
    · subst z₂
      rcases hz₂m with ⟨hz₂u, hz₂nv⟩ | ⟨hz₂v, hz₂nu⟩
      · exact hnouv (-z₁) (hnegA hz₁A) hz₁nu hz₂nv
      · exact hnouv z₁ hz₁A hz₁u hz₂v
    · subst z₂
      rcases hz₂m with ⟨hz₂u, hz₂nv⟩ | ⟨hz₂v, hz₂nu⟩
      · exact hnouv z₁ hz₁A hz₁u (by simpa using hz₂nv)
      · exact hnouv (-z₁) (hnegA hz₁A) hz₁nu hz₂v
  have hdisjVM : (T ∩ OV) ∩ (T ∩ OM) = ∅ := by
    rw [hTV, hTM, Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨z₁, ⟨hz₁A, hz₁v, hz₁nv⟩, rfl⟩, ⟨z₂, ⟨hz₂A, hz₂m⟩, hz₂eq⟩⟩
    rcases hkey z₁ z₂ hz₂eq.symm with h | h
    · subst z₂
      rcases hz₂m with ⟨hz₂u, hz₂nv⟩ | ⟨hz₂v, hz₂nu⟩
      · exact hnouv z₁ hz₁A hz₂u hz₁v
      · exact hnouv (-z₁) (hnegA hz₁A) hz₂nu hz₁nv
    · subst z₂
      rcases hz₂m with ⟨hz₂u, hz₂nv⟩ | ⟨hz₂v, hz₂nu⟩
      · exact hnouv (-z₁) (hnegA hz₁A) hz₂u hz₁nv
      · exact hnouv z₁ hz₁A (by simpa using hz₂nu) hz₁v
  have h0A : (0 : ℂ) ∈ A := by rw [hmemA]; simpa using h0
  rcases hAuv h0A with h0u | h0v
  · have hsep := hT OU (OV ∪ OM) hOU (hOV.union hOM) hcover
    have hn1 : (T ∩ OU).Nonempty := ⟨0, h0, ⟨0, ⟨h0u, by simpa using h0u⟩, by norm_num⟩⟩
    have hn2 : (T ∩ (OV ∪ OM)).Nonempty := by
      obtain ⟨zv, hzvA, hzvv⟩ := hAv
      rcases hAuv (hnegA hzvA) with hnzu | hnzvv
      · exact ⟨zv ^ (2 : ℕ), hzvA, Or.inr ⟨zv, Or.inr ⟨hzvv, hnzu⟩, rfl⟩⟩
      · exact ⟨zv ^ (2 : ℕ), hzvA, Or.inl ⟨zv, ⟨hzvv, hnzvv⟩, rfl⟩⟩
    obtain ⟨y, hyT, hyOU, hyrest⟩ := hsep hn1 hn2
    rcases hyrest with hyOV | hyOM
    · exact Set.notMem_empty y (hdisjUV ▸ (⟨⟨hyT, hyOU⟩, hyT, hyOV⟩ : y ∈ (T ∩ OU) ∩ (T ∩ OV)))
    · exact Set.notMem_empty y (hdisjUM ▸ (⟨⟨hyT, hyOU⟩, hyT, hyOM⟩ : y ∈ (T ∩ OU) ∩ (T ∩ OM)))
  · have hcover' : T ⊆ OV ∪ (OU ∪ OM) := by
      intro w hw; rcases hcover hw with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    have hsep := hT OV (OU ∪ OM) hOV (hOU.union hOM) hcover'
    have hn1 : (T ∩ OV).Nonempty := ⟨0, h0, ⟨0, ⟨h0v, by simpa using h0v⟩, by norm_num⟩⟩
    have hn2 : (T ∩ (OU ∪ OM)).Nonempty := by
      obtain ⟨zu, hzuA, hzuu⟩ := hAu
      rcases hAuv (hnegA hzuA) with hnzuu | hnzuv
      · exact ⟨zu ^ (2 : ℕ), hzuA, Or.inl ⟨zu, ⟨hzuu, hnzuu⟩, rfl⟩⟩
      · exact ⟨zu ^ (2 : ℕ), hzuA, Or.inr ⟨zu, Or.inl ⟨hzuu, hnzuv⟩, rfl⟩⟩
    obtain ⟨y, hyT, hyOV, hyrest⟩ := hsep hn1 hn2
    rcases hyrest with hyOU | hyOM
    · exact Set.notMem_empty y (hdisjUV ▸ (⟨⟨hyT, hyOU⟩, hyT, hyOV⟩ : y ∈ (T ∩ OU) ∩ (T ∩ OV)))
    · exact Set.notMem_empty y (hdisjVM ▸ (⟨⟨hyT, hyOV⟩, hyT, hyOM⟩ : y ∈ (T ∩ OV) ∩ (T ∩ OM)))

namespace Bottcher

/-- **The filled-Julia sublevel sets are preconnected.** For a parameter whose critical value never
escapes (`hc : ∀ n, c ∉ escapeLevel c n`, i.e. `c ∈ mandelbrot`), every complement of an escape level
`C_n = (escapeLevel c n)ᶜ` is preconnected. Base: `C_0` is the closed disk of radius `max 2 ‖c‖`.
Step: `C_{n+1} = f_c⁻¹(C_n) = {z | z² ∈ (C_n − c)}` with `0 ∈ C_n − c ⟺ c ∈ C_n = hc n`, closed by
`isPreconnected_sq_preimage`. -/
theorem isPreconnected_escapeLevel_compl (c : ℂ) (hc : ∀ n, c ∉ escapeLevel c n) :
    ∀ n, IsPreconnected ((escapeLevel c n)ᶜ) := by
  intro n
  induction n with
  | zero =>
    rw [escapeLevel_zero]
    have hball : (escapeOpen c)ᶜ = Metric.closedBall (0 : ℂ) (max 2 ‖c‖) := by
      ext z
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, escapeOpen,
        Set.mem_setOf_eq, not_lt]
    rw [hball]
    exact (convex_closedBall _ _).isPreconnected
  | succ k ih =>
    set Ck : Set ℂ := (escapeLevel c k)ᶜ with hCk
    set T : Set ℂ := (fun w => w + c) ⁻¹' Ck with hT
    have hTpre : IsPreconnected T := by
      have hTeq : T = (fun w => w - c) '' Ck := by
        ext w
        constructor
        · intro hw; exact ⟨w + c, hw, by ring⟩
        · rintro ⟨x, hx, rfl⟩
          show (x - c) + c ∈ Ck
          rwa [sub_add_cancel]
      rw [hTeq]
      exact ih.image _ (by fun_prop : Continuous (fun w : ℂ => w - c)).continuousOn
    have h0T : (0 : ℂ) ∈ T := by
      show (0 : ℂ) + c ∈ Ck
      rw [zero_add]; exact hc k
    have hEq : (escapeLevel c (k + 1))ᶜ = {z : ℂ | z ^ (2 : ℕ) ∈ T} := by
      rw [escapeLevel_succ]
      ext z
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq, hT, hCk, quadratic_apply]
    rw [hEq]
    exact isPreconnected_sq_preimage hTpre h0T

end Bottcher
