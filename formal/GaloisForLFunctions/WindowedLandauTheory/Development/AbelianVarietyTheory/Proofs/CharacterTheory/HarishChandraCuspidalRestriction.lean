import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.TwoBlockHarishChandraInduction
import Mathlib.LinearAlgebra.Trace
import Mathlib.RepresentationTheory.Invariants

/-! The Harish–Chandra restriction is computed by averaging over a Levi
fibre. For a cuspidal character the averaging operator vanishes. -/

noncomputable section
open scoped Classical

open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

private theorem sum_endomorphisms_eq_zero_of_sum_character_eq_zero
    {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (h : ∑ x, ρ.character x = 0) : ∑ x, ρ x = 0 := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  letI := invertibleOfNonzero hcard
  have he : ρ.averageMap = (Fintype.card G : ℂ)⁻¹ • ∑ x, ρ x := by
    simp only [Representation.averageMap, GroupAlgebra.average, invOf_eq_inv, map_smul, map_sum,
      MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one]
  have ht : LinearMap.trace ℂ V ρ.averageMap = 0 := by
    rw [he, map_smul, map_sum]
    change (Fintype.card G : ℂ)⁻¹ • (∑ x, ρ.character x) = 0
    rw [h, smul_zero]
  have hz := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero
    ρ.isProj_averageMap.isIdempotentElem ht
  rw [he] at hz
  exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero hcard)

private theorem sum_levi_fibre {P L : Type} [Group P] [Fintype P] [Group L] [DecidableEq L]
    (π : P →* L) [Fintype π.ker] (p : P) (f : P → ℂ) :
    (∑ x : P, if π x = π p then f x else 0) = ∑ u : π.ker, f (p * u.val) := by
  calc
    _ = ∑ x : P, if π (p * x) = π p then f (p * x) else 0 :=
      (Equiv.sum_comp (Equiv.mulLeft p) (fun x => if π x = π p then f x else 0)).symm
    _ = ∑ x : P, if x ∈ π.ker then f (p * x) else 0 := by
      refine Finset.sum_congr rfl fun x _ => if_congr ?_ rfl rfl
      rw [MonoidHom.mem_ker, map_mul, mul_eq_left]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun x => by simp) (fun x => f (p * x))

private theorem sum_fibre_character_eq_zero {P L V : Type}
    [Group P] [Fintype P] [Group L] [DecidableEq L] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : P →* L) [Fintype π.ker] (ρ : Representation ℂ P V) (hN : ∑ x : π.ker, ρ x.val = 0) (l : L) :
    (∑ x : P, if π x = l then ρ.character x else 0) = 0 := by
  by_cases h : ∃ p : P, π p = l
  · obtain ⟨p, hp⟩ := h
    rw [← hp, sum_levi_fibre π p ρ.character]
    calc
      (∑ x : π.ker, ρ.character (p * x.val)) =
          ∑ x : π.ker, LinearMap.trace ℂ V (ρ p * ρ x.val) :=
        Finset.sum_congr rfl fun x _ => congrArg (LinearMap.trace ℂ V) (map_mul ρ p x.val)
      _ = LinearMap.trace ℂ V (ρ p * ∑ x : π.ker, ρ x.val) := by rw [Finset.mul_sum, map_sum]
      _ = _ := by rw [hN, mul_zero, map_zero]
  · exact Finset.sum_eq_zero fun x _ => if_neg (fun hx => h ⟨x, hx⟩)

private theorem sum_kernel_eq_zero_of_sum_fibre_character_eq_zero {P L V : Type}
    [Group P] [Fintype P] [Group L] [DecidableEq L] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : P →* L) [Fintype π.ker] (ρ : Representation ℂ P V)
    (h : (∑ x : P, if π x = 1 then ρ.character x else 0) = 0) :
    ∑ x : π.ker, ρ x.val = 0 := by
  let σ : Representation ℂ π.ker V := ρ.comp π.ker.subtype
  apply sum_endomorphisms_eq_zero_of_sum_character_eq_zero σ
  calc
    (∑ x : π.ker, σ.character x) =
        ∑ x ∈ Finset.univ.filter (fun x : P => x ∈ π.ker), ρ.character x :=
      (Finset.sum_subtype _ (fun x => by simp) ρ.character).symm
    _ = ∑ x : P, if π x = 1 then ρ.character x else 0 := by
      rw [Finset.sum_filter]
      exact Finset.sum_congr rfl fun x _ => if_congr MonoidHom.mem_ker rfl rfl
    _ = 0 := h

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

private abbrev leviKernel (g a b : ℕ) [Fact g.Prime] :=
  (twoBlockLevi (g := g) (a := a) (b := b)).ker

private abbrev leviKernelFintype (g a b : ℕ) [Fact g.Prime] : Fintype (leviKernel g a b) :=
  Fintype.ofFinite (leviKernel g a b)

/-- The rectangular-matrix definition is a weighted sum over a fibre of the diagonal-block map. -/
theorem res_eq_sum_diagonal_fibre (χ : Gn g (a + b) → ℂ) (u : Gn g a) (v : Gn g b) :
    res a b χ u v = ((g : ℂ) ^ (a * b))⁻¹ *
      ∑ x : twoBlockParabolic g a b, if twoBlockLevi x = (u, v) then χ x.val else 0 := by
  let P := twoBlockParabolic g a b
  let f (x : Gn g (a + b)) :=
    if InPar a (x : Mt g (a + b)) ∧ tl a (x : Mt g (a + b)) = (u : Mt g a) ∧
      br a b (x : Mt g (a + b)) = (v : Mt g b) then χ x else 0
  have h (x : P) : f x.val = if twoBlockLevi x = (u, v) then χ x.val else 0 := by
    refine if_congr ?_ rfl rfl
    have hx : InPar a (x.val : Mt g (a + b)) := x.2
    change (InPar a (x.val : Mt g (a + b)) ∧ _ ∧ _) ↔ _
    rw [and_iff_right hx, Prod.ext_iff, Units.ext_iff, Units.ext_iff]
    rfl
  unfold res
  apply congrArg (((g : ℂ) ^ (a * b))⁻¹ * ·)
  change (∑ x, f x) = _
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x => x ∈ P), f x := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ P
      · rw [if_pos hx]
      · rw [if_neg hx]
        exact if_neg (fun h => hx h.1)
    _ = ∑ x : P, f x.val :=
      Finset.sum_subtype _ (fun x => by simp) f
    _ = _ := Finset.sum_congr rfl fun x _ => h x

/-- Degree zero of Harish–Chandra restriction forces the sum of the radical's operators to vanish. -/
theorem sum_leviKernel_eq_zero_of_degree_zero
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Gn g (a + b)) V) (h0 : res a b ρ.character 1 1 = 0) :
    letI := leviKernelFintype g a b
    ∑ x : leviKernel g a b, ρ x.val.val = 0 := by
  let P := twoBlockParabolic g a b
  let π : P →* Gn g a × Gn g b := twoBlockLevi
  letI instN : Fintype π.ker := leviKernelFintype g a b
  let σ : Representation ℂ P V := ρ.comp P.subtype
  let c : ℂ := ((g : ℂ) ^ (a * b))⁻¹
  let s : ℂ := ∑ x : P, if π x = 1 then σ.character x else 0
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero
  have hcs : res a b ρ.character 1 1 = c * s := by
    change res a b ρ.character 1 1 =
      c * ∑ x : P, if π x = ((1 : Gn g a), (1 : Gn g b)) then ρ.character x.val else 0
    exact res_eq_sum_diagonal_fibre ρ.character (1 : Gn g a) (1 : Gn g b)
  have hs : s = 0 := (mul_eq_zero.mp (hcs.symm.trans h0)).resolve_left (inv_ne_zero (pow_ne_zero _ hg))
  have hz : ∑ x : π.ker, σ x.val = 0 :=
    sum_kernel_eq_zero_of_sum_fibre_character_eq_zero π σ hs
  exact hz

/-- If the restriction has degree zero, the parabolic radical has no nonzero fixed vector. -/
theorem eq_zero_of_leviKernel_fixed {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Gn g (a + b)) V) (h0 : res a b ρ.character 1 1 = 0) (v : V)
    (hv : ∀ x : leviKernel g a b, ρ x.val.val v = v) :
    v = 0 := by
  let N := leviKernel g a b
  letI : Fintype N := leviKernelFintype g a b
  have hs := congrArg (fun L : Module.End ℂ V => L v) (sum_leviKernel_eq_zero_of_degree_zero ρ h0)
  have h : (Fintype.card N : ℂ) • v = 0 := by
    simpa only [LinearMap.coe_sum, Finset.sum_apply, hv, Finset.sum_const, Finset.card_univ,
      LinearMap.zero_apply, Nat.cast_smul_eq_nsmul] using hs
  exact (smul_eq_zero.mp h).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- If the Harish–Chandra restriction of a character has degree zero,
averaging gives zero at every Levi element. -/
theorem res_eq_zero_of_degree_zero {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Gn g (a + b)) V) (h0 : res a b ρ.character 1 1 = 0)
    (u : Gn g a) (v : Gn g b) : res a b ρ.character u v = 0 := by
  let P := twoBlockParabolic g a b
  let π : P →* Gn g a × Gn g b := twoBlockLevi
  letI : Fintype π.ker := leviKernelFintype g a b
  let σ : Representation ℂ P V := ρ.comp P.subtype
  have hz : ∑ x : π.ker, σ x.val = 0 := sum_leviKernel_eq_zero_of_degree_zero ρ h0
  have hs := sum_fibre_character_eq_zero π σ hz (u, v)
  let c : ℂ := ((g : ℂ) ^ (a * b))⁻¹
  calc
    res a b ρ.character u v = c * ∑ x : P, if π x = (u, v) then σ.character x else 0 :=
      res_eq_sum_diagonal_fibre ρ.character u v
    _ = 0 := (congrArg (c * ·) hs).trans (mul_zero c)

/-- The restriction of a cuspidal character vanishes along every proper two-block parabolic. -/
theorem res_cuspidal_eq_zero {n : ℕ} {χ : Gn g n → ℂ} (hχ : IsCusp χ)
    (m : ℕ) (hm : 0 < m) (hm' : m < n) (u : Gn g m) (v : Gn g (n - m)) :
    res m (n - m) χ u v = 0 := by
  obtain ⟨V, _, hV⟩ := hχ.2.1
  have h0 := hχ.2.2 m hm hm'
  generalize hs : n - m = k at v h0 ⊢
  have e : m + k = n := hs ▸ Nat.add_sub_of_le hm'.le
  subst n
  have hchar : Representation.character V.ρ = χ := funext hV
  rw [← hchar] at h0 ⊢
  exact res_eq_zero_of_degree_zero V.ρ h0 u v

end GlobalTheory.GLq
