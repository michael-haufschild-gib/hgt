import GaloisForLFunctions.HTGeometry.HankelTangentSpace
import GaloisForLFunctions.HTGeometry.LinearIndependenceMinorTransfer

/-!
# The square catalecticant cuts out the secant variety

For `N = 2m − 1` and the square Hankel matrix `H_m(h) = (h_{i+j})_{i,j<m}`:

`rank H_m(h) ≤ r ⟺ every (r+1)-minor of H_m(h) vanishes ⟺ h ∈ V(I_r)`,

where `I_r` is the ideal of maximal minors of the `(r+1)`-row Hankel matrix, the ideal of the
closure of the spans of `r` points of the rational normal curve (`mem_secantVariety_iff`).

The nontrivial implication is the rank comparison between Hankel matrices of different shapes.
Read the left kernel of `H_a` as the space `W` of polynomials of degree `< a` annihilating the
window `0, …, N−a`; vanishing `(r+1)`-minors give `dim W ≥ a − r`.  If `G` generates the ideal
spanned by `W`, then `W = G·W'` with `W'` of the same dimension in degree `< a − deg G`, so
`deg G ≤ r`.  The space `W'` has no common factor; over an infinite field it contains an element
`f₁` relatively prime to an element `f₂` of maximal degree `b ≥ a − r − 1`, and Sylvester division
`q = f₂ u + f₁ u' + f₂ v'` with small `u, u', v'` shows `Λ(G q) = 0` for every `q` of degree
`≤ N − a + b`.  So `G` annihilates the long window `0, …, N−1−r`: the `(r+1)`-row Hankel matrix
has a left kernel vector.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

section Kernel

variable {L : Type*} [Field L] {N : ℕ}

theorem AnnihilatesWindow.add {x : Fin N → L} {f g : L[X]} {m : ℕ} (hf : AnnihilatesWindow x f m)
    (hg : AnnihilatesWindow x g m) : AnnihilatesWindow x (f + g) m := fun j hj => by
  rw [add_mul, map_add, hf j hj, hg j hj, add_zero]

theorem AnnihilatesWindow.smul {x : Fin N → L} {f : L[X]} {m : ℕ} (hf : AnnihilatesWindow x f m)
    (c : L) : AnnihilatesWindow x (c • f) m := fun j hj => by
  rw [smul_mul_assoc, map_smul, hf j hj, smul_zero]

/-- The left kernel of the `a`-row Hankel matrix, as polynomials of degree `< a`. -/
def hankelLeftKernel (x : Fin N → L) (a : ℕ) : Submodule L L[X] where
  carrier := {f | f.degree < a ∧ AnnihilatesWindow x f (N - a)}
  add_mem' hf hg := ⟨(degree_add_le _ _).trans_lt (max_lt hf.1 hg.1), hf.2.add hg.2⟩
  zero_mem' := ⟨by simp, fun j _ => by simp⟩
  smul_mem' c f hf := ⟨(degree_smul_le c f).trans_lt hf.1, hf.2.smul c⟩

theorem hankelLeftKernel_le (x : Fin N → L) (a : ℕ) : hankelLeftKernel x a ≤ degreeLT L a :=
  fun _ hf => mem_degreeLT.mpr hf.1

instance (x : Fin N → L) (a : ℕ) : FiniteDimensional L (hankelLeftKernel x a) :=
  haveI : FiniteDimensional L (degreeLT L a) := LinearEquiv.finiteDimensional (degreeLTEquiv L a).symm
  Submodule.finiteDimensional_of_le (hankelLeftKernel_le x a)

theorem finrank_degreeLT_eq (L : Type*) [Field L] (n : ℕ) : Module.finrank L (degreeLT L n) = n := by
  rw [(degreeLTEquiv L n).finrank_eq, Module.finrank_fin_fun]

theorem finrank_le_of_le_degreeLT {W : Submodule L L[X]} {n : ℕ} (h : W ≤ degreeLT L n) :
    Module.finrank L W ≤ n := by
  haveI : FiniteDimensional L (degreeLT L n) :=
    LinearEquiv.finiteDimensional (degreeLTEquiv L n).symm
  exact (Submodule.finrank_mono h).trans (finrank_degreeLT_eq L n).le

/-- **The rank comparison.**  If the left kernel of the `a`-row Hankel matrix has dimension at least
`a − r`, `r < a`, `2a ≤ N + 1`, then some nonzero polynomial of degree `≤ r` annihilates the window
`0, …, N−1−r`. -/
theorem exists_annihilator_of_le_finrank [Infinite L] (x : Fin N → L) {a r : ℕ} (hra : r < a)
    (haN : 2 * a ≤ N + 1) (hdim : a - r ≤ Module.finrank L (hankelLeftKernel x a)) :
    ∃ g : L[X], g ≠ 0 ∧ g.natDegree ≤ r ∧ AnnihilatesWindow x g (N - 1 - r) := by
  classical
  set W := hankelLeftKernel x a with hWdef
  have hW0 : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  -- the generator of the ideal spanned by `W`, made monic
  set IW : Ideal L[X] := Ideal.span (W : Set L[X]) with hIWdef
  set G₀ := Submodule.IsPrincipal.generator IW
  have hIW : IW = Ideal.span {G₀} := (Ideal.span_singleton_generator IW).symm
  have hG₀ : G₀ ≠ 0 := by
    intro h0
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have : w ∈ IW := Ideal.subset_span hw
    rw [hIW, h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
    exact (Submodule.mem_bot L).mpr this
  set G := G₀ * C G₀.leadingCoeff⁻¹ with hGdef
  have hGm : G.Monic := monic_mul_leadingCoeff_inv hG₀
  have hIWG : IW = Ideal.span {G} := by
    rw [hIW, hGdef, Ideal.span_singleton_mul_right_unit]
    exact isUnit_C.mpr (IsUnit.inv (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hG₀)))
  have hdvd : ∀ w ∈ W, G ∣ w := fun w hw =>
    Ideal.mem_span_singleton.mp (hIWG ▸ Ideal.subset_span hw)
  set e := G.natDegree
  -- `W = G · W'`
  set W' := W.comap (LinearMap.mulLeft L G) with hW'def
  have hmulinj : Function.Injective (LinearMap.mulLeft L G) := mul_right_injective₀ hGm.ne_zero
  have hmapW' : W'.map (LinearMap.mulLeft L G) = W := by
    rw [hW'def, Submodule.map_comap_eq, inf_eq_right]
    intro w hw
    obtain ⟨u, rfl⟩ := hdvd w hw
    exact ⟨u, rfl⟩
  have hfin : Module.finrank L W' = Module.finrank L W := by
    rw [← hmapW']
    exact (Submodule.equivMapOfInjective _ hmulinj W').finrank_eq
  have hmemW' : ∀ u, u ∈ W' ↔ G * u ∈ W := fun u => Iff.rfl
  have hdegW : ∀ w ∈ W, w.natDegree ≤ a - 1 ∨ w = 0 := by
    intro w hw
    by_cases hw0 : w = 0
    · exact Or.inr hw0
    · left
      have := hw.1
      rw [degree_eq_natDegree hw0] at this
      have : w.natDegree < a := by exact_mod_cast this
      omega
  -- `deg G ≤ a − 1`
  have he : e ≤ a - 1 := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    obtain ⟨u, rfl⟩ := hdvd w hw
    have hu0 : u ≠ 0 := by rintro rfl; simp at hw0
    rcases hdegW _ hw with h | h
    · rw [hGm.natDegree_mul' (by simpa [hGm.leadingCoeff] using hu0)] at h
      omega
    · exact absurd h hw0
  have hdegW' : ∀ u ∈ W', u.natDegree + e ≤ a - 1 := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0, natDegree_zero, zero_add]; exact he
    rcases hdegW _ ((hmemW' u).mp hu) with h | h
    · rw [hGm.natDegree_mul' (by simpa [hGm.leadingCoeff] using hu0)] at h
      omega
    · exact absurd ((mul_eq_zero.mp h).resolve_left hGm.ne_zero) hu0
  -- `deg G ≤ r`
  have hW'le : W' ≤ degreeLT L (a - e) := by
    intro u hu
    rw [mem_degreeLT]
    by_cases hu0 : u = 0
    · rw [hu0, degree_zero]; exact WithBot.bot_lt_coe _
    rw [degree_eq_natDegree hu0]
    have := hdegW' u hu
    exact_mod_cast (show u.natDegree < a - e by omega)
  have her : e ≤ r := by
    have := finrank_le_of_le_degreeLT hW'le
    omega
  -- `W'` generates the unit ideal
  have hone : (1 : L[X]) ∈ Ideal.span (W' : Set L[X]) := by
    have key : ∀ z ∈ IW, ∃ s ∈ Ideal.span (W' : Set L[X]), z = G * s := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem w hw =>
          obtain ⟨u, rfl⟩ := hdvd w hw
          exact ⟨u, Ideal.subset_span ((hmemW' u).mpr hw), rfl⟩
      | zero => exact ⟨0, Submodule.zero_mem _, by rw [mul_zero]⟩
      | add y z _ _ hy hz =>
          obtain ⟨s, hs, rfl⟩ := hy
          obtain ⟨t, ht, rfl⟩ := hz
          exact ⟨s + t, Submodule.add_mem _ hs ht, by ring⟩
      | smul c z _ hz =>
          obtain ⟨s, hs, rfl⟩ := hz
          exact ⟨c * s, Ideal.mul_mem_left _ c hs, by rw [smul_eq_mul]; ring⟩
    obtain ⟨s, hs, hGs⟩ := key G (hIWG ▸ Ideal.mem_span_singleton_self G)
    have : s = 1 := mul_left_cancel₀ hGm.ne_zero (hGs.symm.trans (mul_one G).symm)
    exact this ▸ hs
  -- an element `f₂` of large degree
  set d := Module.finrank L W'
  have hd : a - r ≤ d := hfin ▸ hdim
  obtain ⟨f₂, hf₂W, hf₂0, hf₂deg⟩ : ∃ f ∈ W', f ≠ 0 ∧ d - 1 ≤ f.natDegree := by
    by_contra hall
    push Not at hall
    have hle : W' ≤ degreeLT L (d - 1) := by
      intro f hf
      rw [mem_degreeLT]
      by_cases hf0 : f = 0
      · rw [hf0, degree_zero]; exact WithBot.bot_lt_coe _
      rw [degree_eq_natDegree hf0]
      exact_mod_cast hall f hf hf0
    have := finrank_le_of_le_degreeLT hle
    omega
  -- an element `f₁` relatively prime to `f₂`
  obtain ⟨f₁, hf₁W, hcop⟩ : ∃ f ∈ W', IsCoprime f f₂ := by
    set F := (UniqueFactorizationMonoid.normalizedFactors f₂).toFinset
    let p : F → Submodule L W' := fun q =>
      ((Ideal.span {(q : L[X])}).restrictScalars L).comap W'.subtype
    have hp : ∀ q, p q ≠ ⊤ := by
      intro q hq
      have hqprime := UniqueFactorizationMonoid.prime_of_normalized_factor (q : L[X])
        (Multiset.mem_toFinset.mp q.2)
      have hle : (W' : Set L[X]) ⊆ Ideal.span {(q : L[X])} := by
        intro u hu
        have : (⟨u, hu⟩ : W') ∈ p q := hq ▸ Submodule.mem_top
        exact this
      have h1 := Ideal.span_le.mpr hle hone
      exact hqprime.not_unit (Ideal.span_singleton_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h1))
    obtain ⟨⟨f, hfW⟩, hf⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
    refine ⟨f, hfW, IsRelPrime.isCoprime fun c hcf hcf₂ => ?_⟩
    by_contra hc
    obtain ⟨q, hq, hqc⟩ := WfDvdMonoid.exists_irreducible_factor hc
      (fun h0 => hf₂0 (zero_dvd_iff.mp (h0 ▸ hcf₂)))
    obtain ⟨q', hq'F, hqq'⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hf₂0 hq (hqc.trans hcf₂)
    apply hf ⟨q', Multiset.mem_toFinset.mpr hq'F⟩
    show f ∈ Ideal.span {q'}
    exact Ideal.mem_span_singleton.mpr (hqq'.symm.dvd.trans (hqc.trans hcf))
  -- Sylvester division
  have hGW : ∀ u ∈ W', AnnihilatesWindow x (G * u) (N - a) := fun u hu => ((hmemW' u).mp hu).2
  set b := f₂.natDegree
  have hb : b + e ≤ a - 1 := hdegW' f₂ hf₂W
  have hf₁deg : f₁.natDegree + e ≤ a - 1 := hdegW' f₁ hf₁W
  have hΛ : ∀ q : L[X], q.natDegree ≤ N - a + b → momentFunctional x (G * q) = 0 := by
    intro q hq
    set f₂m := f₂ * C f₂.leadingCoeff⁻¹ with hf₂m
    have hf₂mm : f₂m.Monic := monic_mul_leadingCoeff_inv hf₂0
    have hf₂mdeg : f₂m.natDegree = b := by
      rw [hf₂m, natDegree_mul_C (inv_ne_zero (leadingCoeff_ne_zero.mpr hf₂0))]
    have hf₂mW : f₂m ∈ W' := by
      have := W'.smul_mem f₂.leadingCoeff⁻¹ hf₂W
      rwa [smul_eq_C_mul, mul_comm] at this
    set u := q /ₘ f₂m
    set rem := q %ₘ f₂m
    have hq' : q = f₂m * u + rem := by rw [add_comm]; exact (modByMonic_add_div q f₂m).symm
    have hudeg : u.natDegree ≤ N - a := by
      rw [natDegree_divByMonic _ hf₂mm, hf₂mdeg]; omega
    have h1 : momentFunctional x (G * (f₂m * u)) = 0 := by
      rw [← mul_assoc]; exact (hGW f₂m hf₂mW).mul hudeg
    -- the remainder
    have h2 : momentFunctional x (G * rem) = 0 := by
      by_cases hb0 : b = 0
      · have : rem = 0 := by
          have hlt := degree_modByMonic_lt q hf₂mm
          rw [degree_eq_natDegree hf₂mm.ne_zero, hf₂mdeg, hb0] at hlt
          exact degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hlt)
        rw [this, mul_zero, map_zero]
      obtain ⟨α, β, hαβ⟩ := hcop
      set u' := (rem * α) %ₘ f₂m
      set Q := (rem * α) /ₘ f₂m
      set v' := C f₂.leadingCoeff⁻¹ * Q * f₁ + rem * β
      have hrem : rem = f₁ * u' + f₂ * v' := by
        have h3 : rem * α = f₂m * Q + u' := by rw [add_comm]; exact (modByMonic_add_div _ f₂m).symm
        calc rem = rem * (α * f₁ + β * f₂) := by rw [hαβ, mul_one]
          _ = (rem * α) * f₁ + rem * β * f₂ := by ring
          _ = (f₂m * Q + u') * f₁ + rem * β * f₂ := by rw [h3]
          _ = f₁ * u' + f₂ * v' := by rw [hf₂m]; ring
      have hu'deg : u'.natDegree < b := by
        have := natDegree_modByMonic_lt (rem * α) hf₂mm
          (by intro h; rw [h, natDegree_one] at hf₂mdeg; omega)
        rwa [hf₂mdeg] at this
      have hremdeg : rem.natDegree < b := by
        have := natDegree_modByMonic_lt q hf₂mm
          (by intro h; rw [h, natDegree_one] at hf₂mdeg; omega)
        rwa [hf₂mdeg] at this
      have hv'deg : v'.natDegree ≤ N - a := by
        by_cases hv0 : v' = 0
        · rw [hv0, natDegree_zero]; exact Nat.zero_le _
        have hfv : (f₂ * v').natDegree = b + v'.natDegree := natDegree_mul hf₂0 hv0
        have hfv' : f₂ * v' = rem - f₁ * u' := by rw [hrem]; ring
        have hle : (rem - f₁ * u').natDegree ≤ (b - 1) + f₁.natDegree := by
          refine (natDegree_sub_le _ _).trans (max_le (by omega) ?_)
          exact natDegree_mul_le.trans (by omega)
        rw [hfv'] at hfv
        omega
      rw [hrem, mul_add, map_add, ← mul_assoc, ← mul_assoc,
        (hGW f₁ hf₁W).mul (by omega), (hGW f₂ hf₂W).mul hv'deg, add_zero]
    rw [hq', mul_add, map_add, h1, h2, add_zero]
  refine ⟨G, hGm.ne_zero, her, fun j hj => hΛ _ ?_⟩
  rw [natDegree_X_pow]
  omega

/-! ## Minors and the dimension of the left kernel -/

/-- **Vanishing `(r+1)`-minors bound the row span.**  If every `(r+1)`-minor of a matrix over a field
vanishes, its rows span a space of dimension at most `r`. -/
theorem finrank_span_rows_le_of_minors {a b : ℕ} (M : Matrix (Fin a) (Fin b) L) (r : ℕ)
    (hmin : ∀ (R : Fin (r + 1) → Fin a) (C : Fin (r + 1) → Fin b), (M.submatrix R C).det = 0) :
    Module.finrank L (Submodule.span L (Set.range M)) ≤ r := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨S, hS, hSspan, hSind⟩ := exists_linearIndependent L (Set.range M)
  haveI : Fintype S := Set.Finite.fintype ((Set.finite_range M).subset hS)
  have h1 : Module.finrank L (Submodule.span L S) = S.toFinset.card :=
    finrank_span_set_eq_card hSind
  rw [hSspan] at h1
  have hcard : r + 1 ≤ S.toFinset.card := by omega
  obtain ⟨T, hT, hTcard⟩ := Finset.exists_subset_card_eq hcard
  -- choose `r+1` rows
  have hrow : ∀ y : T, ∃ i, M i = y := fun y => hS (Set.mem_toFinset.mp (hT y.2))
  choose R hR using hrow
  set e := T.equivFin.symm with he
  set Rf : Fin (r + 1) → Fin a := fun k => R (e (Fin.cast hTcard.symm k)) with hRf
  have hind : LinearIndependent L (fun k => M (Rf k)) := by
    have h1 : LinearIndependent L (fun y : T => (y : Fin b → L)) :=
      hSind.comp (fun y : T => (⟨y, Set.mem_toFinset.mp (hT y.2)⟩ : S))
        (fun y z h => Subtype.ext (congrArg Subtype.val h :))
    have h2 := h1.comp (fun k => e (Fin.cast hTcard.symm k))
      (e.injective.comp (Fin.cast_injective _))
    convert h2 using 1
    funext k
    simp only [hRf, Function.comp]
    exact hR _
  obtain ⟨φ, hφ⟩ := exists_coordinateMinor_det_ne_zero_fin (r + 1) _ hind
  apply hφ
  have := hmin Rf φ
  rw [← Matrix.det_transpose] at this
  convert this using 2
  ext i j
  rfl

/-- **A nonzero `(r+1)`-minor gives `r + 1` independent rows.** -/
theorem lt_finrank_span_rows_of_minor {a b : ℕ} (M : Matrix (Fin a) (Fin b) L) {r : ℕ}
    (R : Fin (r + 1) → Fin a) (C : Fin (r + 1) → Fin b) (h : (M.submatrix R C).det ≠ 0) :
    r < Module.finrank L (Submodule.span L (Set.range M)) := by
  classical
  have hind : LinearIndependent L (fun k => M (R k)) :=
    linearIndependent_rows_of_det_submatrix_ne_zero (M := M.submatrix R id) (s := C)
      (by simpa using h)
  have h1 := hind.fintype_card_le_finrank
  have h2 : Module.finrank L (Submodule.span L (Set.range fun k => M (R k))) ≤
      Module.finrank L (Submodule.span L (Set.range M)) :=
    Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range R M))
  rw [finrank_span_eq_card hind, Fintype.card_fin] at h2
  omega

/-- **Vanishing `(r+1)`-minors give a large left kernel.** -/
theorem le_finrank_hankelLeftKernel (x : Fin N → L) {a r : ℕ} (haN : a ≤ N)
    (hmin : ∀ (R : Fin (r + 1) → Fin a) (C : Fin (r + 1) → Fin (N + 1 - a)),
      Matrix.det (fun i j => x ⟨R i + C j, by have := (R i).isLt; have := (C j).isLt; omega⟩) = 0) :
    a - r ≤ Module.finrank L (hankelLeftKernel x a) := by
  classical
  set M : Matrix (Fin a) (Fin (N + 1 - a)) L :=
    fun i c => x ⟨i + c, by have := i.isLt; have := c.isLt; omega⟩ with hM
  have hrank := finrank_span_rows_le_of_minors M r hmin
  have hrange : LinearMap.range (Fintype.linearCombination L M) =
      Submodule.span L (Set.range M) := Fintype.range_linearCombination L M
  have hrn := LinearMap.finrank_range_add_finrank_ker (Fintype.linearCombination L M)
  rw [hrange, Module.finrank_fin_fun] at hrn
  -- the kernel embeds in the left kernel
  set ι : LinearMap.ker (Fintype.linearCombination L M) →ₗ[L] hankelLeftKernel x a :=
    { toFun := fun c => ⟨vecPoly (c : Fin a → L), by
        refine ⟨?_, fun j hj => ?_⟩
        · rcases Nat.eq_zero_or_pos a with ha | ha
          · subst ha; simp [vecPoly]
          · refine (degree_le_natDegree).trans_lt ?_
            have := natDegree_vecPoly_le (c : Fin a → L)
            exact_mod_cast (show (vecPoly (c : Fin a → L)).natDegree < a by omega)
        · rw [momentFunctional_vecPoly_mul_X_pow x _ (by omega)]
          have hc : Fintype.linearCombination L M (c : Fin a → L) = 0 := c.2
          have := congrFun hc ⟨j, by omega⟩
          rw [Fintype.linearCombination_apply] at this
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hM, Pi.zero_apply] at this
          rw [← this]⟩
      map_add' := fun c d => Subtype.ext (by simp [vecPoly, Finset.sum_add_distrib, add_mul])
      map_smul' := fun c d => Subtype.ext (by
        simp [vecPoly, Finset.mul_sum, smul_eq_C_mul, mul_assoc]) }
  have hιinj : Function.Injective ι := by
    intro c d hcd
    have := congrArg (fun f : hankelLeftKernel x a => (f : L[X])) hcd
    simp only [ι, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact Subtype.ext (funext fun i => by rw [← coeff_vecPoly (c : Fin a → L) i, this,
      coeff_vecPoly])
  have := LinearMap.finrank_le_finrank_of_injective hιinj
  omega

end Kernel

/-! ## The square catalecticant -/

section Secant

variable (K : Type) [Field K]

/-- A nonzero polynomial of degree `≤ r` annihilating the long window kills every maximal minor of
the `(r+1)`-row Hankel matrix. -/
theorem det_eq_zero_of_annihilator {N r : ℕ} (x : Fin N → K) {g : K[X]} (hg0 : g ≠ 0)
    (hgdeg : g.natDegree ≤ r) (hgw : AnnihilatesWindow x g (N - 1 - r)) (c : Fin (r + 1) → ℕ)
    (hbound : ∀ j, (r + 1) + c j ≤ N) :
    Matrix.det (fun i j : Fin (r + 1) => x (RHTower.finiteHankelIndex c hbound i j)) = 0 := by
  classical
  set v : Fin (r + 1) → K := fun i => g.coeff i
  have hv0 : v ≠ 0 := by
    intro h
    apply hg0
    rw [← vecPoly_coeff (h := g) (r := r + 1) (by omega),
      show (fun i : Fin (r + 1) => g.coeff i) = 0 from h]
    simp [vecPoly]
  refine Matrix.exists_vecMul_eq_zero_iff.mp ⟨v, hv0, ?_⟩
  funext j
  have hj := hgw (c j) (by have := hbound j; omega)
  rw [← vecPoly_coeff (h := g) (r := r + 1) (show g.natDegree < r + 1 by omega),
    momentFunctional_vecPoly_mul_X_pow x _ (hbound j)] at hj
  simpa [Matrix.vecMul, dotProduct, RHTower.finiteHankelIndex, v] using hj

/-- **Vanishing square `(r+1)`-minors put the point on the secant variety.** -/
theorem secantIdeal_eval_eq_zero_of_squareMinors [CharZero K] {m r : ℕ} (hrm : r < m)
    (h : Fin (2 * m - 1) → K)
    (hmin : ∀ R C : Fin (r + 1) → Fin m, Matrix.det (fun i j =>
      h ⟨R i + C j, by have := (R i).isLt; have := (C j).isLt; omega⟩) = 0) :
    ∀ g ∈ RHTower.finiteHankelSecantIdeal K (2 * m - 1) r, MvPolynomial.eval h g = 0 := by
  classical
  haveI : Infinite K := CharZero.infinite K
  have hm : 2 * m - 1 + 1 - m = m := by omega
  have hdim := le_finrank_hankelLeftKernel h (a := m) (r := r) (by omega) fun R C => by
    have := hmin R (fun j => Fin.cast hm (C j))
    convert this using 3
    rfl
  obtain ⟨g, hg0, hgdeg, hgw⟩ := exists_annihilator_of_le_finrank h hrm (by omega) hdim
  have hle : RHTower.finiteHankelSecantIdeal K (2 * m - 1) r ≤ RingHom.ker (MvPolynomial.eval h) := by
    rw [RHTower.finiteHankelSecantIdeal, Ideal.span_le]
    rintro _ ⟨c, hbound, -, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, RHTower.finiteHankelMaximalMinorOver, RingHom.map_det]
    have := det_eq_zero_of_annihilator K h hg0 hgdeg hgw c hbound
    convert this using 2
    ext i j
    simp
  exact fun g hg => hle hg

/-- Points of the secant variety have vanishing square `(r+1)`-minors. -/
theorem squareMinors_eq_zero_of_secant {m r : ℕ} (h : Fin (2 * m - 1) → K)
    (hh : ∀ g ∈ RHTower.finiteHankelSecantIdeal K (2 * m - 1) r, MvPolynomial.eval h g = 0)
    (R C : Fin (r + 1) → Fin m) :
    Matrix.det (fun i j =>
      h ⟨R i + C j, by have := (R i).isLt; have := (C j).isLt; omega⟩) = 0 := by
  have hmem := hankelMinor_mem_secantIdeal K (N := 2 * m - 1) (s := r) (fun i => R i)
    (fun j => C j) (fun i j => by have := (R i).isLt; have := (C j).isLt; omega)
  have := hh _ hmem
  rw [RingHom.map_det] at this
  convert this using 2
  ext i j
  simp

/-- **The catalecticant theorem `(5)`.**  For the square Hankel matrix `H_m(h) = (h_{i+j})` of a
point `h` of `K^{2m−1}` and `r < m`:

`rank H_m(h) ≤ r ⟺ every (r+1)-minor of H_m(h) vanishes ⟺ h ∈ V(I_r)`. -/
theorem squareCatalecticant_iff [CharZero K] {m r : ℕ} (hrm : r < m) (h : Fin (2 * m - 1) → K) :
    ((Matrix.of fun i j : Fin m =>
        h ⟨i + j, by have := i.isLt; have := j.isLt; omega⟩).rank ≤ r ↔
      ∀ R C : Fin (r + 1) → Fin m, Matrix.det (fun i j =>
        h ⟨R i + C j, by have := (R i).isLt; have := (C j).isLt; omega⟩) = 0) ∧
    ((∀ R C : Fin (r + 1) → Fin m, Matrix.det (fun i j =>
        h ⟨R i + C j, by have := (R i).isLt; have := (C j).isLt; omega⟩) = 0) ↔
      ∀ g ∈ RHTower.finiteHankelSecantIdeal K (2 * m - 1) r, MvPolynomial.eval h g = 0) := by
  classical
  set H := Matrix.of fun i j : Fin m => h ⟨i + j, by have := i.isLt; have := j.isLt; omega⟩
  refine ⟨⟨fun hrank R C => ?_, fun hmin => ?_⟩, ⟨secantIdeal_eval_eq_zero_of_squareMinors K hrm h,
    fun hh => squareMinors_eq_zero_of_secant K h hh⟩⟩
  · by_contra hne
    have := lt_finrank_span_rows_of_minor H R C hne
    have hrank' : Module.finrank K (Submodule.span K (Set.range H)) ≤ r := by
      rw [Matrix.rank_eq_finrank_span_row] at hrank
      exact hrank
    omega
  · rw [Matrix.rank_eq_finrank_span_row]
    exact finrank_span_rows_le_of_minors H r hmin

/-- The point `x_n = Σ_j c_j t_j^n` of `r` atoms. -/
def atomMomentPoint {r : ℕ} (N : ℕ) (c t : Fin r → K) : Fin N → K :=
  fun n => ∑ j, c j * t j ^ (n : ℕ)

theorem eval_secantParameterization {N r : ℕ} (pt : Fin r × Fin 2 → K)
    (f : MvPolynomial (Fin N) K) :
    MvPolynomial.eval pt (RHTower.finiteHankelSecantParameterization K N r f) =
      MvPolynomial.eval (atomMomentPoint K N (fun j => pt (j, 0)) (fun j => pt (j, 1))) f := by
  have h : (MvPolynomial.eval pt).comp (RHTower.finiteHankelSecantParameterization K N r) =
      MvPolynomial.eval (atomMomentPoint K N (fun j => pt (j, 0)) (fun j => pt (j, 1))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) fun n => ?_
    · simp [RHTower.finiteHankelSecantParameterization, RHTower.deningerHankelSecantParameterization]
    · simp [RHTower.deningerHankelSecantMoment, atomMomentPoint]
  exact congrArg (fun φ : MvPolynomial (Fin N) K →+* K => φ f) h

/-- **The secant variety is the closure of the spans of `r` points of the rational normal curve**:
`h ∈ V(I_r)` exactly when every polynomial vanishing at all `r`-atom moment points vanishes at
`h`. -/
theorem mem_secantVariety_iff [Infinite K] (N r : ℕ) (h : Fin N → K) :
    (∀ g ∈ RHTower.finiteHankelSecantIdeal K N r, MvPolynomial.eval h g = 0) ↔
      ∀ f : MvPolynomial (Fin N) K,
        (∀ c t : Fin r → K, MvPolynomial.eval (atomMomentPoint K N c t) f = 0) → MvPolynomial.eval h f = 0 := by
  constructor
  · intro hh f hf
    refine hh f ?_
    rw [RHTower.finiteHankelSecantIdeal_eq_parameterization_ker, RingHom.mem_ker]
    refine MvPolynomial.funext fun pt => ?_
    rw [eval_secantParameterization, map_zero]
    exact hf _ _
  · intro hh g hg
    refine hh g fun c t => ?_
    rw [RHTower.finiteHankelSecantIdeal_eq_parameterization_ker, RingHom.mem_ker] at hg
    have := eval_secantParameterization K (N := N) (r := r)
      (fun a => if a.2 = 0 then c a.1 else t a.1) g
    rw [hg, map_zero] at this
    simpa using this.symm

end Secant

end

end GaloisForLFunctions.HTGeometry
