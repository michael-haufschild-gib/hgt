import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpForwardHull

/-!
# Without bounded vectors the inverse contracts a lattice

Let `T` be a uniformizer-semilinear automorphism of a finite-dimensional completed skew vector space
and `W` a `T`-stable subspace containing no nonzero vector with bounded forward orbit.  Then `T⁻¹`
contracts some lattice `P` of `W` uniformly: `ϖ^{-1} P ⊆ T^m P` for one `m ≥ 1`
(`DiffOp.exists_contracting_lattice_of_inf_forwardBoundedSubspace_eq_bot`).

The proof is a strong induction on `dim W`.  Take a lattice `Λ` of `W`, its forward hull `M` and the
divisible part `W'` of `M`.  If `W' = W` the exhaustion lemma produces the contracting lattice.
Otherwise `W'` is a smaller stable subspace, so by induction `T⁻¹` contracts a lattice `P₁` of `W'`;
by the divisible-part lemma `M` is bounded modulo `W'`.  The **splitting lemma**
`DiffOp.exists_sub_mem_forwardBoundedSubspace_of_contracting` then corrects every vector of a lattice
bounded modulo `W'` by an element of `W'` into a vector with bounded forward orbit: the correction is
the convergent series `t₀ = Σ_i T^{-(i+1)} w_i` of the defects `w_i = T u_i - u_{i+1}` of an orbit
`u_i` kept inside the lattice, and the shifted tails `t_n` satisfy `T t_n = w_n + t_{n+1}`, whence
`Tⁿ(u - t₀) = u_n - t_n` stays bounded.  Since `W` has no bounded vectors, the lattice lies in `W'`,
so `W = W'` after all.

The quantitative contraction `T^{-j} P ⊆ ϖ^{⌊j/m⌋ - b} P` (`DiffOp.exists_inv_pow_le_uniformizerDilate`)
drives the convergence; continuity of `T` on a lattice (`DiffOp.exists_semilinearImage_le_shift`) and
uniqueness of limits identify the tails.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K]

attribute [local instance] completedPseudoDiffOpIntegerSMul

variable {E : Type*} [AddCommGroup E] [Module (CompletedPseudoDiffOp K) E]
  [FiniteDimensional (CompletedPseudoDiffOp K) E]

section Images

variable {S : E ≃ₗ[ℤ] E} {M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E}

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem semilinearImage_pow_add (hS : IsUniformizerSemilinear (K := K) S) (a b : ℕ) :
    semilinearImage (S ^ (a + b)) (hS.pow (a + b)) M =
      semilinearImage (S ^ a) (hS.pow a) (semilinearImage (S ^ b) (hS.pow b) M) := by
  ext y
  rw [mem_semilinearImage, mem_semilinearImage, mem_semilinearImage, pow_add, mul_inv_rev,
    LinearEquiv.mul_apply]

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- An automorphism preserving the span of a lattice moves its dilations by a bounded shift. -/
theorem exists_semilinearImage_le_shift (hS : IsUniformizerSemilinear (K := K) S)
    {P : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (hP : P.FG)
    (hSP : ∀ x ∈ Submodule.span (CompletedPseudoDiffOp K) (P : Set E),
      S x ∈ Submodule.span (CompletedPseudoDiffOp K) (P : Set E)) :
    ∃ c : ℕ, ∀ k : ℤ, semilinearImage S hS (uniformizerDilate k P) ≤
      uniformizerDilate (k - c) P := by
  obtain ⟨c, hc⟩ := exists_nat_le_uniformizerDilate_of_fg (M := P)
    (N := semilinearImage S hS P) (semilinearImage_fg hP) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_semilinearImage_iff_exists.1 hy
      exact hSP x (Submodule.subset_span hx))
  refine ⟨c, fun k => ?_⟩
  rw [semilinearImage_uniformizerDilate]
  refine (uniformizerDilate_mono hc).trans ?_
  rw [uniformizerDilate_uniformizerDilate, sub_eq_add_neg]

end Images

variable {T : E ≃ₗ[ℤ] E} (hT : IsUniformizerSemilinear (K := K) T)

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
theorem semilinearImage_pow_congr {S : E ≃ₗ[ℤ] E} (hS : IsUniformizerSemilinear (K := K) S)
    {M : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} {a b : ℕ} (h : a = b) :
    semilinearImage (S ^ a) (hS.pow a) M = semilinearImage (S ^ b) (hS.pow b) M := by
  subst h
  rfl

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- The contraction `ϖ^{-1} P ⊆ T^m P` says `T^{-m} P ⊆ ϖ P`. -/
theorem inv_pow_le_uniformizerDilate_one_of_contracting
    {P : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} {m : ℕ}
    (hcontr : uniformizerDilate (-1) P ≤ semilinearImage (T ^ m) (hT.pow m) P) :
    semilinearImage (T⁻¹ ^ m) (hT.inv.pow m) P ≤ uniformizerDilate 1 P := by
  have h := semilinearImage_mono (hT := hT.inv.pow m) hcontr
  have hback : semilinearImage (T⁻¹ ^ m) (hT.inv.pow m)
      (semilinearImage (T ^ m) (hT.pow m) P) = P := by
    ext y
    rw [mem_semilinearImage, mem_semilinearImage, inv_pow, inv_inv, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply]
  rw [hback, semilinearImage_uniformizerDilate] at h
  have := uniformizerDilate_le_iff.1 h
  rwa [neg_neg] at this

omit [FiniteDimensional (CompletedPseudoDiffOp K) E] in
/-- A contraction `ϖ^{-1} P ⊆ T^m P` gives the quantitative bound `T^{-j} P ⊆ ϖ^{⌊j/m⌋ - b} P`. -/
theorem exists_inv_pow_le_uniformizerDilate
    {P : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (hP : P.FG)
    (hPinv : ∀ x ∈ Submodule.span (CompletedPseudoDiffOp K) (P : Set E),
      T⁻¹ x ∈ Submodule.span (CompletedPseudoDiffOp K) (P : Set E))
    {m : ℕ} (hm : 1 ≤ m)
    (hcontr : uniformizerDilate (-1) P ≤ semilinearImage (T ^ m) (hT.pow m) P) :
    ∃ b : ℕ, ∀ j : ℕ, semilinearImage (T⁻¹ ^ j) (hT.inv.pow j) P ≤
      uniformizerDilate (((j / m : ℕ) : ℤ) - b) P := by
  classical
  have hstep := inv_pow_le_uniformizerDilate_one_of_contracting hT hcontr
  have hmul : ∀ q : ℕ, semilinearImage (T⁻¹ ^ (m * q)) (hT.inv.pow (m * q)) P ≤
      uniformizerDilate (q : ℤ) P := by
    intro q
    induction q with
    | zero =>
        intro y hy
        rw [mem_semilinearImage, Nat.mul_zero, pow_zero, inv_one] at hy
        rw [Nat.cast_zero, uniformizerDilate_zero]
        exact hy
    | succ q ih =>
        rw [semilinearImage_pow_congr hT.inv (show m * (q + 1) = m + m * q by ring),
          semilinearImage_pow_add hT.inv]
        refine (semilinearImage_mono ih).trans ?_
        rw [semilinearImage_uniformizerDilate]
        refine (uniformizerDilate_mono hstep).trans ?_
        rw [uniformizerDilate_uniformizerDilate, Nat.cast_succ, add_comm]
  have hspan : ∀ r : ℕ, ∀ x ∈ Submodule.span (CompletedPseudoDiffOp K) (P : Set E),
      (T⁻¹ ^ r) x ∈ Submodule.span (CompletedPseudoDiffOp K) (P : Set E) := by
    intro r
    induction r with
    | zero => intro x hx; rwa [pow_zero]
    | succ r ih =>
        intro x hx
        rw [pow_succ', LinearEquiv.mul_apply]
        exact hPinv _ (ih x hx)
  have hfin : ∀ r : ℕ, ∃ br : ℕ, semilinearImage (T⁻¹ ^ r) (hT.inv.pow r) P ≤
      uniformizerDilate (-(br : ℤ)) P := by
    intro r
    exact exists_nat_le_uniformizerDilate_of_fg (semilinearImage_fg hP) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_semilinearImage_iff_exists.1 hy
      exact hspan r x (Submodule.subset_span hx))
  choose br hbr using hfin
  refine ⟨(Finset.range m).sup br, fun j => ?_⟩
  rw [semilinearImage_pow_congr hT.inv (Nat.mod_add_div j m).symm, semilinearImage_pow_add hT.inv]
  refine (semilinearImage_mono (hmul _)).trans ?_
  rw [semilinearImage_uniformizerDilate]
  refine (uniformizerDilate_mono (hbr _)).trans ?_
  rw [uniformizerDilate_uniformizerDilate]
  refine uniformizerDilate_antitone P ?_
  have hmem : j % m ∈ Finset.range m := Finset.mem_range.2 (Nat.mod_lt j (by omega))
  have hle : br (j % m) ≤ (Finset.range m).sup br := Finset.le_sup hmem
  omega

/-- **Splitting lemma.**  Let `W₁` be a stable subspace on which `T⁻¹` contracts a lattice, and let
`N` be a finitely generated integral submodule stable under `T` modulo `W₁`.  Then every vector of
`N` differs from a vector with bounded forward orbit by an element of `W₁`. -/
theorem exists_sub_mem_forwardBoundedSubspace_of_contracting
    {W₁ : Submodule (CompletedPseudoDiffOp K) E}
    {P₁ : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (hP₁ : P₁.FG)
    (hP₁W : Submodule.span (CompletedPseudoDiffOp K) (P₁ : Set E) = W₁)
    (hW₁ : ∀ x ∈ W₁, T x ∈ W₁) (hW₁' : ∀ x ∈ W₁, T⁻¹ x ∈ W₁)
    {m : ℕ} (hm : 1 ≤ m)
    (hcontr : uniformizerDilate (-1) P₁ ≤ semilinearImage (T ^ m) (hT.pow m) P₁)
    {N : Submodule (CompletedPseudoDiffOpInteger (K := K)) E} (hN : N.FG)
    (hTN : semilinearImage T hT N ≤ N ⊔ W₁.restrictScalars (CompletedPseudoDiffOpInteger (K := K)))
    {u : E} (hu : u ∈ N) :
    ∃ w ∈ W₁, u - w ∈ forwardBoundedSubspace T hT := by
  classical
  subst hP₁W
  obtain ⟨b, hb⟩ := exists_inv_pow_le_uniformizerDilate hT hP₁ hW₁' hm hcontr
  obtain ⟨c₁, hc₁⟩ := exists_semilinearImage_le_shift hT hP₁ hW₁
  -- the defects live in a finitely generated submodule of `W₁`
  set R := (semilinearImage T hT N ⊔ N) ⊓
    (Submodule.span (CompletedPseudoDiffOp K) (P₁ : Set E)).restrictScalars
      (CompletedPseudoDiffOpInteger (K := K)) with hRdef
  have hRfg : R.FG := ((semilinearImage_fg hN).sup hN).of_le inf_le_left
  obtain ⟨a, ha⟩ := exists_nat_le_uniformizerDilate_of_fg (M := P₁) hRfg
    (fun x hx => hx.2)
  have hstep : ∀ x ∈ N, ∃ x' ∈ N, T x - x' ∈ R := by
    intro x hx
    have hTx := hTN (apply_mem_semilinearImage (hT := hT) hx)
    obtain ⟨x', hx', w, hw, hxw⟩ := Submodule.mem_sup.1 hTx
    refine ⟨x', hx', ?_, ?_⟩
    · refine Submodule.sub_mem _ (Submodule.mem_sup_left (apply_mem_semilinearImage hx))
        (Submodule.mem_sup_right hx')
    · rw [← hxw, add_sub_cancel_left]
      exact hw
  choose! nxt hnxt hdef using hstep
  let us : ℕ → E := fun j => nxt^[j] u
  have hus : ∀ j, us j ∈ N := by
    intro j
    induction j with
    | zero => exact hu
    | succ j ih =>
        change nxt^[j + 1] u ∈ N
        rw [Function.iterate_succ_apply']
        exact hnxt _ ih
  have hus_succ : ∀ j, us (j + 1) = nxt (us j) := by
    intro j
    change nxt^[j + 1] u = nxt (nxt^[j] u)
    rw [Function.iterate_succ_apply']
  let ws : ℕ → E := fun j => T (us j) - us (j + 1)
  have hws : ∀ j, ws j ∈ R := by
    intro j
    change T (us j) - us (j + 1) ∈ R
    rw [hus_succ]
    exact hdef _ (hus j)
  -- the correction series and its shifted tails
  let z : ℕ → ℕ → E := fun n i => (T⁻¹ ^ (i + 1)) (ws (n + i))
  have hz : ∀ n i, z n i ∈ uniformizerDilate ((((i + 1) / m : ℕ) : ℤ) - b - a) P₁ := by
    intro n i
    have h1 : z n i ∈ semilinearImage (T⁻¹ ^ (i + 1)) (hT.inv.pow (i + 1)) R :=
      apply_mem_semilinearImage (hws (n + i))
    have h2 := semilinearImage_mono (hT := hT.inv.pow (i + 1)) ha h1
    rw [semilinearImage_uniformizerDilate] at h2
    have h3 := uniformizerDilate_mono (k := -(a : ℤ)) (hb (i + 1)) h2
    rw [uniformizerDilate_uniformizerDilate] at h3
    convert h3 using 2
    ring
  set Q := uniformizerDilate (-((a : ℤ) + b)) P₁ with hQdef
  have hzQ : ∀ n i, z n i ∈ Q := fun n i =>
    uniformizerDilate_antitone P₁ (by
      have h0 : (0 : ℤ) ≤ (((i + 1) / m : ℕ) : ℤ) := Nat.cast_nonneg _
      linarith) (hz n i)
  let s : ℕ → ℕ → E := fun n N => ∑ i ∈ Finset.range N, z n i
  have hsQ : ∀ n N, s n N ∈ Q := fun n N => Submodule.sum_mem _ fun i _ => hzQ n i
  have hlim : ∀ n, ∃ t, ∀ k : ℕ, ∀ᶠ N in atTop, t - s n N ∈ uniformizerDilate (k : ℤ) P₁ := by
    intro n
    refine exists_limit_of_eventually_sub_mem_uniformizerDilate hP₁ (s n) fun k => ?_
    refine eventually_atTop.2 ⟨m * (k + a + b), fun N hN => ?_⟩
    have hdiff : s n (N + 1) - s n N = z n N := by
      simp only [s, Finset.sum_range_succ, add_sub_cancel_left]
    rw [hdiff]
    refine uniformizerDilate_antitone P₁ ?_ (hz n N)
    have : k + a + b ≤ (N + 1) / m := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      nlinarith
    omega
  choose t ht using hlim
  have htQ : ∀ n, t n ∈ Q := by
    intro n
    obtain ⟨N, hN⟩ := (ht n 0).exists
    rw [Nat.cast_zero, uniformizerDilate_zero] at hN
    have hPQ : P₁ ≤ Q := by
      have := uniformizerDilate_antitone P₁ (show -((a : ℤ) + b) ≤ 0 by omega)
      rwa [uniformizerDilate_zero] at this
    have := Submodule.add_mem _ (hPQ hN) (hsQ n N)
    rwa [sub_add_cancel] at this
  -- the tail recursion `T t_n = w_n + t_{n+1}`
  have hTs : ∀ n N, T (s n (N + 1)) = ws n + s (n + 1) N := by
    intro n N
    simp only [s]
    rw [Finset.sum_range_succ', _root_.map_add, _root_.map_sum, add_comm]
    congr 1
    · simp only [z, add_zero, zero_add, pow_one]
      rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [z]
      rw [pow_succ', LinearEquiv.mul_apply, ← LinearEquiv.mul_apply T, mul_inv_cancel,
        LinearEquiv.coe_one, id, show n + (i + 1) = n + 1 + i by ring]
  have htail : ∀ n, T (t n) = ws n + t (n + 1) := by
    intro n
    refine eq_of_eventually_sub_mem_uniformizerDilate hP₁ (s := fun N => ws n + s (n + 1) N)
      (fun k => ?_) (fun k => ?_)
    · filter_upwards [(tendsto_add_atTop_nat 1).eventually (ht n (k + c₁))] with N hN
      rw [← hTs, ← _root_.map_sub]
      have := hc₁ ((k + c₁ : ℕ) : ℤ) (apply_mem_semilinearImage (hT := hT) hN)
      convert this using 2
      push_cast
      ring
    · filter_upwards [ht (n + 1) k] with N hN
      rwa [add_sub_add_left_eq_sub]
  -- the corrected orbit
  have horbit : ∀ n, (T ^ n) (u - t 0) = us n - t n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, _root_.map_sub, htail]
        change T (us n) - (T (us n) - us (n + 1) + t (n + 1)) = us (n + 1) - t (n + 1)
        abel
  refine ⟨t 0, ?_, ?_⟩
  · have := uniformizerDilate_subset_span (M := P₁) (-((a : ℤ) + b)) (htQ 0)
    exact this
  · refine ⟨N ⊔ Q, hN.sup (uniformizerDilate_fg _ hP₁), fun n => ?_⟩
    rw [horbit]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (hus n)) (Submodule.mem_sup_right (htQ n))

/-- **Without bounded vectors the inverse contracts a lattice.**  If a subspace `W`, stable under
`T` and `T⁻¹`, contains no nonzero vector with bounded forward orbit, then `T⁻¹` contracts some
lattice of `W`: `ϖ^{-1} P ⊆ T^m P` for one `m ≥ 1`. -/
theorem exists_contracting_lattice_of_inf_forwardBoundedSubspace_eq_bot :
    ∀ (n : ℕ) (W : Submodule (CompletedPseudoDiffOp K) E),
      Module.finrank (CompletedPseudoDiffOp K) W = n →
      (∀ x ∈ W, T x ∈ W) → (∀ x ∈ W, T⁻¹ x ∈ W) → forwardBoundedSubspace T hT ⊓ W = ⊥ →
      ∃ P : Submodule (CompletedPseudoDiffOpInteger (K := K)) E, P.FG ∧
        Submodule.span (CompletedPseudoDiffOp K) (P : Set E) = W ∧ ∃ m : ℕ, 1 ≤ m ∧
          uniformizerDilate (-1) P ≤ semilinearImage (T ^ m) (hT.pow m) P := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hWn hfwd hinv hB
  obtain ⟨d, e, c, he, hsum, hδ⟩ := exists_coordinates W
  have hspan := span_span_range_eq he hsum
  set Λ := Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range e) with hΛdef
  have hΛfg : Λ.FG :=
    ⟨Finset.univ.image e, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
  have hΛW : Λ ≤ W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
    rw [hΛdef, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact he i
  have hMW : forwardHullSup hT Λ ≤ W.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) :=
    iSup_le fun k => forwardHull_le_of_invariant hT hΛW hfwd k
  set W' := divisiblePart (forwardHullSup hT Λ) with hW'def
  have hW'W : W' ≤ W := fun x hx => hMW (divisiblePart_le hx)
  by_cases hWW' : W ≤ W'
  · obtain ⟨P, hPfg, hΛP, hPW, m, hm, hcontr⟩ := exists_contracting_of_le_divisiblePart hT hΛfg
      (by rw [hspan]; exact hfwd) (by rw [hspan]; exact hinv) (by rw [hspan]; exact hWW')
    refine ⟨P, hPfg, le_antisymm ?_ ?_, m, hm, hcontr⟩
    · rw [Submodule.span_le, ← hspan]
      exact hPW
    · rw [← hspan]
      exact Submodule.span_mono hΛP
  · have hlt : W' < W := lt_of_le_of_ne hW'W (fun h => hWW' h.symm.le)
    have hfin : Module.finrank (CompletedPseudoDiffOp K) W' < n :=
      hWn ▸ Submodule.finrank_lt_finrank_of_lt hlt
    -- stability of the divisible part
    have hTM : ∀ x ∈ forwardHullSup hT Λ, T x ∈ forwardHullSup hT Λ :=
      fun x hx => apply_mem_forwardHullSup hT hx
    have hfwd' : ∀ x ∈ W', T x ∈ W' := by
      intro x hx k
      have hk := hx k
      rw [mem_uniformizerDilate] at hk ⊢
      rw [← IsUniformizerSemilinear.map_uniformizerZPow_smul hT]
      exact hTM _ hk
    have hinv' : ∀ x ∈ W', T⁻¹ x ∈ W' := by
      have hle : semilinearSubspaceImage T hT W' ≤ W' := by
        intro y hy
        rw [mem_semilinearSubspaceImage] at hy
        have := hfwd' _ hy
        rwa [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] at this
      have heq := semilinearSubspaceImage_eq_of_le hle
      intro x hx
      rw [← heq] at hx
      exact hx
    have hB' : forwardBoundedSubspace T hT ⊓ W' = ⊥ :=
      eq_bot_iff.2 (hB ▸ inf_le_inf_left _ hW'W)
    obtain ⟨P₁, hP₁fg, hP₁W, m, hm, hcontr⟩ := ih _ hfin W' rfl hfwd' hinv' hB'
    obtain ⟨c', hc'⟩ := exists_le_divisiblePart_sup_uniformizerDilate hΛfg
      (le_forwardHullSup hT) (fun x hx => by rw [hspan]; exact hMW hx)
    set N := forwardHullSup hT Λ ⊓ uniformizerDilate (-(c' : ℤ)) Λ with hNdef
    have hNfg : N.FG := (uniformizerDilate_fg _ hΛfg).of_le inf_le_right
    have hMN : forwardHullSup hT Λ ≤ N ⊔ W'.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
      intro x hx
      obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.1 (hc' hx)
      have hzM : z ∈ forwardHullSup hT Λ := by
        have : z = x - w := by rw [← hwz]; abel
        rw [this]
        exact Submodule.sub_mem _ hx (divisiblePart_le hw)
      rw [← hwz, add_comm]
      exact Submodule.add_mem_sup ⟨hzM, hz⟩ hw
    have hTN : semilinearImage T hT N ≤
        N ⊔ W'.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_semilinearImage_iff_exists.1 hy
      exact hMN (hTM x hx.1)
    have hNW' : N ≤ W'.restrictScalars (CompletedPseudoDiffOpInteger (K := K)) := by
      intro u hu
      obtain ⟨w, hw, hbdd⟩ := exists_sub_mem_forwardBoundedSubspace_of_contracting hT hP₁fg hP₁W
        hfwd' hinv' hm hcontr hNfg hTN hu
      have huW : u - w ∈ W := Submodule.sub_mem _ (hMW hu.1) (hW'W hw)
      have hzero : u - w ∈ forwardBoundedSubspace T hT ⊓ W := ⟨hbdd, huW⟩
      rw [hB, Submodule.mem_bot, sub_eq_zero] at hzero
      rw [hzero]
      exact hw
    exfalso
    apply hWW'
    rw [← hspan, Submodule.span_le]
    intro x hx
    exact (hMN.trans (sup_le hNW' le_rfl)) (le_forwardHullSup hT hx)

end

end DiffOp

end GaloisForLFunctions.HTGeometry
