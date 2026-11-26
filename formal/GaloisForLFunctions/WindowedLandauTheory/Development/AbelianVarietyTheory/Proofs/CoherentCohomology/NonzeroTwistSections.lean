import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.TwistGlobalExtension
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.InvertibleTwistPowers

/-! A local section on a nonempty affine nonvanishing open supplies
nonzero global sections in all sufficiently large twists. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LineBundleSections

variable {X : Scheme.{0}} {M H : LB X}

private theorem exists_ne_zero_section_of_affine (hM : M.IsLB)
    {V : X.Opens} (hV : IsAffineOpen V) (h : (V : Set X).Nonempty) :
    ∃ a : Γ(toMod M, V), a ≠ 0 := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1
    (hM.cover.ge (show x ∈ (⊤ : X.Opens) from trivial))
  obtain ⟨u, hu, hxu⟩ := hV.exists_basicOpen_le (⟨x, hi⟩ : M.U i) hx
  let W := X.basicOpen u
  let e := chartEquiv hM i hu
  letI : (toMod M).IsQuasicoherent := isQuasicoherent_toMod hM
  let z : Γ(toMod M, W) := e.symm 1
  obtain ⟨n, a, ha⟩ := (hasBasicOpenLocalization_of_isQuasicoherent (toMod M) hV u).1 z
  refine ⟨a, fun hz => ?_⟩
  subst a
  have e₀ := congrArg e ha
  have eu : IsUnit (resG X (X.basicOpen_le u) u) := X.toRingedSpace.isUnit_res_basicOpen u
  have hzero : (resG X (X.basicOpen_le u) u) ^ n = 0 := by
    simpa only [map_smul, map_zero, z, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one] using e₀
  let g := (X.presheaf.germ W x hxu).hom
  exact ((eu.pow n).map g).ne_zero ((congrArg g hzero).trans g.map_zero)

private theorem mulTwistPower_ne_zero {V : X.Opens} {d t : ℤ}
    (s : (transitionPower H d).Sec) (hV : V ≤ nonzeroLocus s) (k : ℕ)
    {a : Γ(toMod (twist M H t), V)} (ha : a ≠ 0) : mulTwistPower M s k t V a ≠ 0 := by
  intro h
  exact ha ((mulTwistPower_bijective s hV k).1 (h.trans (map_zero _).symm))

/-- The nonvanishing open of the power section is affine and nonempty, so it has a
nonzero local section. Clearing denominators extends it after a sufficiently large twist. -/
theorem exists_nonzero_high_twist [CompactSpace X] [X.IsSeparated] {d : ℤ}
    (hM : M.IsLB) (hH : H.IsLB) (s : (transitionPower H d).Sec)
    (hV : IsAffineOpen (nonzeroLocus s)) (hV' : (nonzeroLocus s : Set X).Nonempty) :
    ∃ k : ℕ, ∀ j : ℕ, k ≤ j → ∃ b : Γ(toMod (twist M H ((j : ℤ) * d)), ⊤), b ≠ 0 := by
  let V := nonzeroLocus s
  obtain ⟨a, ha⟩ := exists_ne_zero_section_of_affine (twist_isLB hM hH 0) hV hV'
  obtain ⟨k, b, hb⟩ := exists_global_lift_mulTwistPower hM hH s a
  have hbV : (toMod (twist M H (0 + (k : ℤ) * d))).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op b ≠ 0 :=
    hb.symm ▸ mulTwistPower_ne_zero s le_rfl k ha
  refine ⟨k, fun j hj => ?_⟩
  let c := mulTwistPower M s (j - k) (0 + (k : ℤ) * d) ⊤ b
  have hc : c ≠ 0 := by
    intro hz
    have he := mulTwistPower_restrict s (j - k) (0 + (k : ℤ) * d) (le_top : V ≤ ⊤) b
    have he' := mulTwistPower_ne_zero s (V := V) le_rfl (j - k) hbV
    apply he'
    exact he.trans ((congrArg _ hz).trans (map_zero _))
  have hd : 0 + (k : ℤ) * d + ((j - k : ℕ) : ℤ) * d = (j : ℤ) * d := by
    rw [zero_add, ← add_mul, ← Nat.cast_add, Nat.add_sub_of_le hj]
  have hex : ∃ a : Γ(toMod (twist M H (0 + (k : ℤ) * d + ((j - k : ℕ) : ℤ) * d)), ⊤), a ≠ 0 :=
    ⟨c, hc⟩
  exact hd ▸ hex

end GlobalTheory.LineBundleSections
