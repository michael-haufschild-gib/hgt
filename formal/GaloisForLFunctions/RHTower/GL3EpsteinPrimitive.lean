import GaloisForLFunctions.RHTower.GL3EpsteinEisenstein
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Analysis.PSeries


/-!
# The Epstein zeta function of `h³` over primitive vectors

Every nonzero `v ∈ ℤ³` is uniquely `d w` with `d = gcd(v) ≥ 1` and `w` primitive (`primScale`,
`primScale_injective`, `range_primScale`), and `Q_z(d w) = d² Q_z(w)` (`qf_smul`). Hence, for
`s > 3/2`, `Z_z(s) = ζ(2s) · Σ_{w primitive} Q_z(w)^{-s}` (`epstein_eq_zeta_mul_prim`), the form in
which the maximal parabolic Eisenstein series is a sum over the bottom rows of `SL₃(ℤ)`.
-/

open Matrix

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### Primitive vectors -/

/-- A vector of `ℤ³` is primitive when its entries have gcd `1`. -/
def IsPrim (w : Fin 3 → ℤ) : Prop := Finset.univ.gcd w = 1

/-- The primitive vectors. -/
abbrev Prim := {w : Fin 3 → ℤ // IsPrim w}

theorem gcd_zero_vec : Finset.univ.gcd (0 : Fin 3 → ℤ) = 0 :=
  Finset.gcd_eq_zero_iff.2 fun _ _ => rfl

theorem prim_ne_zero (w : Prim) : (w : Fin 3 → ℤ) ≠ 0 := by
  intro h
  have := w.2
  unfold IsPrim at this
  rw [h, gcd_zero_vec] at this
  exact zero_ne_one this

/-- `(d, w) ↦ d w`. -/
def primScale (p : ℕ+ × Prim) : Fin 3 → ℤ := ((p.1 : ℕ) : ℤ) • (p.2 : Fin 3 → ℤ)

theorem gcd_primScale (p : ℕ+ × Prim) : Finset.univ.gcd (primScale p) = ((p.1 : ℕ) : ℤ) := by
  have h : Finset.univ.gcd (fun i => ((p.1 : ℕ) : ℤ) * (p.2 : Fin 3 → ℤ) i) =
      normalize ((p.1 : ℕ) : ℤ) * Finset.univ.gcd (p.2 : Fin 3 → ℤ) := Finset.gcd_mul_left
  rw [p.2.2, mul_one, Int.normalize_of_nonneg (by positivity)] at h
  exact h

theorem primScale_injective : Function.Injective primScale := by
  rintro ⟨d, w⟩ ⟨d', w'⟩ h
  have hd : ((d : ℕ) : ℤ) = ((d' : ℕ) : ℤ) := by
    rw [← gcd_primScale (d, w), ← gcd_primScale (d', w'), h]
  have hdd : d = d' := PNat.coe_injective (by exact_mod_cast hd)
  subst hdd
  have hw : (w : Fin 3 → ℤ) = w' := by
    ext i
    have := congrFun h i
    simp only [primScale, Pi.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ (by positivity) this
  exact Prod.ext rfl (Subtype.ext hw)

theorem range_primScale : Set.range primScale = {v | v ≠ 0} := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    intro h
    have := gcd_primScale p
    rw [h, gcd_zero_vec] at this
    exact p.1.ne_zero (by exact_mod_cast this.symm)
  · intro hv
    obtain ⟨g, hg, hg1⟩ := Finset.extract_gcd v Finset.univ_nonempty
    have hne : Finset.univ.gcd v ≠ 0 := by
      rw [Ne, Finset.gcd_eq_zero_iff]
      intro h; exact hv (funext fun i => h i (Finset.mem_univ _))
    have hnn : 0 ≤ Finset.univ.gcd v :=
      Int.nonneg_of_normalize_eq_self Finset.normalize_gcd
    have hpos : 0 < (Finset.univ.gcd v).toNat := by omega
    refine ⟨(⟨(Finset.univ.gcd v).toNat, hpos⟩, ⟨g, hg1⟩), ?_⟩
    ext i
    simp only [primScale, Pi.smul_apply, smul_eq_mul, PNat.mk_coe, Int.toNat_of_nonneg hnn]
    exact (hg i (Finset.mem_univ _)).symm

/-! ### The Epstein zeta function over primitive vectors -/

theorem qf_smul (z : H3) (d : ℤ) (w : Fin 3 → ℤ) : qf z (d • w) = (d : ℝ) ^ 2 * qf z w := by
  have hv : vR (d • w) = (d : ℝ) • vR w := by ext i; simp [vR]
  simp only [qf, hv, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem summable_prim (z : H3) {s : ℝ} (hs : 3 / 2 < s) :
    Summable fun w : Prim => qf z w ^ (-s) := by
  have h := (summable_epstein z hs).comp_injective (Subtype.val_injective (p := IsPrim))
  refine h.congr fun w => ?_
  simp [prim_ne_zero w]

theorem summable_pnat_rpow {r : ℝ} (hr : 1 < r) :
    Summable fun d : ℕ+ => ((d : ℕ) : ℝ) ^ (-r) := by
  have h := (Real.summable_nat_rpow_inv.2 hr).comp_injective PNat.coe_injective
  refine h.congr fun d => ?_
  simp [Real.rpow_neg (Nat.cast_nonneg _)]

/-- **Primitive decomposition of the Epstein zeta function**:
`Z_z(s) = (Σ_{d ≥ 1} d^{-2s}) · Σ_{w primitive} Q_z(w)^{-s}` for `s > 3/2`. -/
theorem epstein_eq_zeta_mul_prim (z : H3) {s : ℝ} (hs : 3 / 2 < s) :
    epstein z s = (∑' d : ℕ+, ((d : ℕ) : ℝ) ^ (-(2 * s))) * ∑' w : Prim, qf z w ^ (-s) := by
  classical
  -- the sum over nonzero vectors
  have h1 : epstein z s = ∑' v : {v : Fin 3 → ℤ // v ≠ 0}, qf z v ^ (-s) := by
    rw [epstein, ← tsum_subtype_eq_of_support_subset (s := {v : Fin 3 → ℤ | v ≠ 0})]
    · exact tsum_congr fun v => by
        have hv : (v : Fin 3 → ℤ) ≠ 0 := v.2
        simp [hv]
    · intro v hv; simp only [Function.mem_support, ne_eq, ite_eq_left_iff, not_forall] at hv
      exact hv.1
  -- reindex by `(d, w) ↦ d w`
  have hrange : ∀ p : ℕ+ × Prim, primScale p ≠ 0 := fun p h =>
    (Set.ext_iff.1 range_primScale (primScale p)).1 ⟨p, rfl⟩ h
  let e : ℕ+ × Prim ≃ {v : Fin 3 → ℤ // v ≠ 0} :=
    Equiv.ofBijective (fun p => ⟨primScale p, hrange p⟩) ⟨fun p q h =>
      primScale_injective (congrArg Subtype.val h), fun v => by
        obtain ⟨p, hp⟩ := (Set.ext_iff.1 range_primScale v.1).2 v.2
        exact ⟨p, Subtype.ext hp⟩⟩
  rw [h1, ← e.tsum_eq]
  have hterm : ∀ p : ℕ+ × Prim, qf z (e p : Fin 3 → ℤ) ^ (-s) =
      ((p.1 : ℕ) : ℝ) ^ (-(2 * s)) * qf z p.2 ^ (-s) := by
    intro p
    show qf z (primScale p) ^ (-s) = _
    rw [primScale, qf_smul, Real.mul_rpow (by positivity) (qf_nonneg _ _)]
    congr 1
    push_cast
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; push_cast; ring
  rw [tsum_congr hterm, tsum_mul_tsum_of_summable_norm]
  · exact (summable_pnat_rpow (by linarith)).norm
  · exact (summable_prim z hs).norm

end H3
end GaloisForLFunctions.RHTower.GL3
