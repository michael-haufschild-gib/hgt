import GaloisForLFunctions.FamilyContinuationTheory.TheNormCountOfTheEisensteinIntegers
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinPoincareAbsoluteConvergence
import Mathlib

/-!
# The Eisenstein lattice sum is `ζ` times an `L`-function

The zeta function of `ℚ(√−3)`, written as a sum over the nonzero Eisenstein integers, factors:

`Σ_{(m,n) ≠ 0} (m² − mn + n²)^{−s} = 6 ζ(s) L(s, χ₋₃)`  for `Re s > 1`  (`latticeSum_eq`).

This is the transfer from the family over `ℚ(√−3)` to `ζ`: a zero of `ζ` is a zero of the zeta
function of the field. With a Dirichlet character `χ` of the norm the sum is `6 L(s, χ) L(s, χ χ₋₃)`
(`latticeSum_twisted_eq`). The proof regroups the lattice by the norm and uses the norm count
`#{z : N(z) = n} = 6 Σ_{d ∣ n} χ₃(d)`, which is `6 (1 ∗ χ₋₃)(n)`.
-/

open Complex LSeries

namespace GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm

open _root_.RHTower

local notation "𝔼" => RHTower.BourgainEisensteinInt
local notation "N" => RHTower.BourgainEisensteinInt.norm

noncomputable section

/-- The quadratic character of conductor `3`. -/
def chi3D : DirichletCharacter ℂ 3 :=
  (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

theorem chi3D_apply (n : ℕ) : chi3D n = ((chi3 n : ℤ) : ℂ) := by
  have hmod : ((n : ZMod 3)) = ((n % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod n 3).symm
  have h : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have h0 : quadraticChar (ZMod 3) 0 = 0 := by decide
  have h1 : quadraticChar (ZMod 3) 1 = 1 := by decide
  have h2 : quadraticChar (ZMod 3) 2 = -1 := by decide
  rw [chi3D, MulChar.ringHomComp_apply, hmod, chi3]
  interval_cases hn : n % 3
  · simp [h0]
  · simp [h1]
  · simp [h2]

/-- `m² − mn + n²` as a natural number. -/
def latNorm (p : ℤ × ℤ) : ℕ := (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2).toNat

theorem latNorm_cast (p : ℤ × ℤ) : (latNorm p : ℤ) = p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 :=
  Int.toNat_of_nonneg (BourgainEisensteinInt.norm_nonneg ⟨p.1, p.2⟩)

theorem latNorm_pos {p : ℤ × ℤ} (hp : p ≠ (0, 0)) : 0 < latNorm p := by
  have h : (0 : ℤ) < latNorm p := by
    rw [latNorm_cast]
    refine (BourgainEisensteinInt.norm_pos (x := ⟨p.1, p.2⟩)).mpr fun h0 => hp ?_
    exact Prod.ext (congrArg BourgainEisensteinInt.re h0) (congrArg BourgainEisensteinInt.im h0)
  exact_mod_cast h

/-- The lattice terms `(m² − mn + n²)^{−s}` on nonzero pairs. -/
def latTerm (s : ℂ) (p : {p : ℤ × ℤ // p ≠ (0, 0)}) : ℂ := ((latNorm p.1 : ℕ) : ℂ) ^ (-s)

/-- The point `ω = −1/2 + (√3/2) i` in coordinates. -/
def zOmega : D4BMUpperHalfPlaneCoordinate := ⟨-1 / 2, √3 / 2, by positivity⟩

theorem quadratic_zOmega (p : ℤ × ℤ) : d4BMPoincareQuadratic zOmega p = (latNorm p : ℝ) := by
  have h := congrArg (fun z : ℤ => (z : ℝ)) (latNorm_cast p)
  simp only [Int.cast_natCast] at h
  have h3 : (√3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [h, d4BMPoincareQuadratic, zOmega]
  push_cast
  linear_combination ((p.1 : ℝ) ^ 2 / 4) * h3

theorem summable_latTerm {s : ℂ} (hs : 1 < s.re) : Summable (latTerm s) := by
  refine Summable.of_norm_bounded
    (summable_d4BMPoincareQuadratic_cpow_norm zOmega ⟨s, hs⟩) fun p => ?_
  rw [latTerm, norm_natCast_cpow_of_pos (latNorm_pos p.2), quadratic_zOmega]
  simp

/-- The fiber of `latNorm` over `n ≥ 1` is the set of Eisenstein integers of norm `n`. -/
def fiberEquiv {n : ℕ} (hn : 0 < n) :
    ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {n}) ≃ ↥(normSet n) where
  toFun x := ⟨⟨x.1.1.1, x.1.1.2⟩, mem_normSet.mpr (by
    have h : latNorm x.1.1 = n := x.2
    rw [BourgainEisensteinInt.norm_def]
    show x.1.1.1 ^ 2 - x.1.1.1 * x.1.1.2 + x.1.1.2 ^ 2 = n
    rw [← latNorm_cast, h])⟩
  invFun z := ⟨⟨(z.1.re, z.1.im), fun h => by
      have hz := mem_normSet.mp z.2
      rw [BourgainEisensteinInt.norm_def] at hz
      have h1 : z.1.re = 0 := congrArg Prod.fst h
      have h2 : z.1.im = 0 := congrArg Prod.snd h
      rw [h1, h2] at hz
      have : (n : ℤ) = 0 := by rw [← hz]; ring
      omega⟩, by
    show latNorm (z.1.re, z.1.im) = n
    have hz := mem_normSet.mp z.2
    rw [BourgainEisensteinInt.norm_def] at hz
    have : (latNorm (z.1.re, z.1.im) : ℤ) = n := by rw [latNorm_cast, hz]
    exact_mod_cast this⟩
  left_inv x := rfl
  right_inv z := rfl

theorem tsum_fiber {s : ℂ} (n : ℕ) :
    ∑' b : ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {n}), latTerm s b =
      LSeries.term (fun n => ((normSet n).card : ℂ)) s n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · haveI : IsEmpty ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {0}) :=
      ⟨fun x => (latNorm_pos x.1.2).ne' x.2⟩
    rw [tsum_empty, LSeries.term_zero]
  · have hconst : ∀ b : ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {n}),
        latTerm s b = (n : ℂ) ^ (-s) := fun b => by
      have h : latNorm b.1.1 = n := b.2
      rw [latTerm, h]
    simp_rw [hconst]
    rw [(fiberEquiv hn).tsum_eq (fun _ => (n : ℂ) ^ (-s)), Finset.tsum_subtype (normSet n)
      (fun _ => (n : ℂ) ^ (-s)), Finset.sum_const, LSeries.term_of_ne_zero hn.ne', nsmul_eq_mul,
      cpow_neg, div_eq_mul_inv]

/-- **The zeta function of `ℚ(√−3)`**:
`Σ_{(m,n) ≠ 0} (m² − mn + n²)^{−s} = 6 ζ(s) L(s, χ₋₃)` for `Re s > 1`. -/
theorem latticeSum_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' p, latTerm s p = 6 * (riemannZeta s * DirichletCharacter.LFunction chi3D s) := by
  have hfib := (summable_latTerm hs).hasSum.tsum_fiberwise
    (fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1)
  simp_rw [tsum_fiber] at hfib
  have hL : LSeries (fun n => ((normSet n).card : ℂ)) s = ∑' p, latTerm s p := hfib.tsum_eq
  rw [← hL]
  have hconv : ∀ {n : ℕ}, n ≠ 0 → ((normSet n).card : ℂ) =
      ((6 : ℂ) • convolution 1 (fun n : ℕ => chi3D n)) n := by
    intro n hn
    have h := card_normSet (Nat.pos_of_ne_zero hn)
    have h' : ((normSet n).card : ℂ) = 6 * ((divisorChar n : ℤ) : ℂ) := by exact_mod_cast h
    rw [h', Pi.smul_apply, smul_eq_mul, LSeries.convolution_def]
    congr 1
    have hd := Nat.sum_divisorsAntidiagonal' (fun a b => (1 : ℕ → ℂ) a * chi3D b) (n := n)
    show _ = ∑ p ∈ n.divisorsAntidiagonal, (1 : ℕ → ℂ) p.1 * chi3D p.2
    rw [hd, divisorChar]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Pi.one_apply, one_mul, chi3D_apply]
  rw [LSeries_congr hconv, LSeries_smul, LSeries_convolution'
    (LSeriesSummable_one_iff.mpr hs) (chi3D.LSeriesSummable_of_one_lt_re hs),
    LSeries_one_eq_riemannZeta hs, DirichletCharacter.LFunction_eq_LSeries chi3D hs]

/-! ### Twists by Dirichlet characters -/

theorem tsum_fiber_twisted {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (n : ℕ) :
    ∑' b : ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {n}),
        χ (latNorm b.1.1) * latTerm s b =
      LSeries.term (fun n => χ n * ((normSet n).card : ℂ)) s n := by
  have hconst : ∀ b : ↑((fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1) ⁻¹' {n}),
      χ (latNorm b.1.1) * latTerm s b = χ n * latTerm s b := fun b => by
    have h : latNorm b.1.1 = n := b.2
    rw [h]
  simp_rw [hconst]
  rw [tsum_mul_left, tsum_fiber]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
    ring

/-- **The Hecke `L`-function of `χ ∘ N` over `ℚ(√−3)`**:
`Σ_{(m,n) ≠ 0} χ(m² − mn + n²) (m² − mn + n²)^{−s} = 6 L(s, χ) L(s, χ χ₋₃)` for `Re s > 1`. -/
theorem latticeSum_twisted_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    ∑' p : {p : ℤ × ℤ // p ≠ (0, 0)}, χ (latNorm p.1) * latTerm s p =
      6 * (LSeries (fun n => χ n) s * LSeries (fun n => χ n * chi3D n) s) := by
  have hsum : Summable fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => χ (latNorm p.1) * latTerm s p := by
    refine Summable.of_norm_bounded (summable_latTerm hs).norm fun p => ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
  have hfib := hsum.hasSum.tsum_fiberwise (fun p : {p : ℤ × ℤ // p ≠ (0, 0)} => latNorm p.1)
  simp_rw [tsum_fiber_twisted] at hfib
  have hL : LSeries (fun n => χ n * ((normSet n).card : ℂ)) s =
      ∑' p : {p : ℤ × ℤ // p ≠ (0, 0)}, χ (latNorm p.1) * latTerm s p := hfib.tsum_eq
  rw [← hL]
  have hconv : ∀ {n : ℕ}, n ≠ 0 → χ n * ((normSet n).card : ℂ) =
      ((6 : ℂ) • convolution (fun n : ℕ => χ n) (fun n : ℕ => χ n * chi3D n)) n := by
    intro n hn
    have h := card_normSet (Nat.pos_of_ne_zero hn)
    have h' : ((normSet n).card : ℂ) = 6 * ((divisorChar n : ℤ) : ℂ) := by exact_mod_cast h
    rw [h', Pi.smul_apply, smul_eq_mul, LSeries.convolution_def]
    have hd := Nat.sum_divisorsAntidiagonal'
      (fun a b => (χ a : ℂ) * (χ b * chi3D b)) (n := n)
    beta_reduce
    rw [hd, divisorChar]
    push_cast
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd' => ?_
    have hdvd : d ∣ n := (Nat.mem_divisors.mp hd').1
    have hmul : (χ ((n / d : ℕ) : ZMod q)) * χ (d : ZMod q) = χ (n : ZMod q) := by
      rw [← map_mul, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    rw [chi3D_apply, ← hmul]
    ring
  have hb1 : ∀ n : ℕ, n ≠ 0 → ‖(χ n : ℂ)‖ ≤ 1 := fun n _ => DirichletCharacter.norm_le_one χ _
  have hb2 : ∀ n : ℕ, n ≠ 0 → ‖(χ n : ℂ) * chi3D n‖ ≤ 1 := fun n _ => by
    rw [norm_mul]
    exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
      (DirichletCharacter.norm_le_one chi3D _)
  rw [LSeries_congr hconv, LSeries_smul, LSeries_convolution'
    (LSeriesSummable_of_bounded_of_one_lt_re hb1 hs)
    (LSeriesSummable_of_bounded_of_one_lt_re hb2 hs)]

end

end GaloisForLFunctions.FamilyContinuationTheory.EisensteinNorm
