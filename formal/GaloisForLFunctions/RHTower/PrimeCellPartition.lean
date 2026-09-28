import GaloisForLFunctions.RHTower.SemiprimeWindowCount
import GaloisForLFunctions.RHTower.MobiusCubicGammaAtomJets
import GaloisForLFunctions.RHTower.Sieve.CellMatching

/-!
# Cells of `(R, 2R]` and cellwise matchings of atoms

* The cell index `⌈(n - R)/h⌉ - 1` places every `n > R` in the cell `(R + ih, R + (i+1)h]`.
* A cellwise count comparison gives one injection that keeps every source in its cell.
* With `J = ⌊(log R)^B⌋` cells of width `h = R/J`: `R/(log R)^B ≤ h ≤ 2R/(log R)^B`.
* Atoms in the band `[R, 2R]` obey `‖f_y - f_x‖_δ ≤ 4 C_1 |y - x| R^{-(3+δ)/2}`.
* A matched family of opposite Möbius signs is a literal subsum of the Möbius source.
-/

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.PrimeCells

open RHTower.CubicGamma

/-- The cell of `n` in the partition of `(R, ∞)` into the cells `(R + ih, R + (i+1)h]`. -/
def cellIndex (R h : ℝ) (n : ℕ) : ℕ := ⌈((n : ℝ) - R) / h⌉₊ - 1

theorem cellIndex_spec {R h : ℝ} (hh : 0 < h) {n : ℕ} (hn : R < n) :
    R + cellIndex R h n * h < n ∧ (n : ℝ) ≤ R + (cellIndex R h n + 1) * h := by
  have hx : 0 < ((n : ℝ) - R) / h := div_pos (by linarith) hh
  have hk : ⌈((n : ℝ) - R) / h⌉₊ ≠ 0 := (Nat.ceil_pos.mpr hx).ne'
  obtain ⟨h1, h2⟩ := (Nat.ceil_eq_iff hk).mp rfl
  have hk1 : 1 ≤ ⌈((n : ℝ) - R) / h⌉₊ := Nat.one_le_iff_ne_zero.mpr hk
  unfold cellIndex
  have e : ((⌈((n : ℝ) - R) / h⌉₊ - 1 : ℕ) : ℝ) + 1 = ⌈((n : ℝ) - R) / h⌉₊ := by
    rw [Nat.cast_sub hk1]; push_cast; ring
  constructor
  · rw [lt_div_iff₀ hh] at h1; linarith
  · rw [e]; rw [div_le_iff₀ hh] at h2; linarith

theorem cellIndex_eq {R h : ℝ} (hh : 0 < h) {n i : ℕ} (h1 : R + i * h < n)
    (h2 : (n : ℝ) ≤ R + (i + 1) * h) : cellIndex R h n = i := by
  unfold cellIndex
  have : ⌈((n : ℝ) - R) / h⌉₊ = i + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    push_cast
    constructor
    · rw [lt_div_iff₀ hh]; linarith
    · rw [div_le_iff₀ hh]; linarith
  rw [this, Nat.add_sub_cancel]

theorem cellIndex_lt {R h : ℝ} (hh : 0 < h) {J n : ℕ} (hn : R < n) (hnJ : (n : ℝ) ≤ R + J * h) :
    cellIndex R h n < J := by
  have := (cellIndex_spec hh hn).1
  have h' : (cellIndex R h n : ℝ) * h < J * h := by linarith
  exact_mod_cast lt_of_mul_lt_mul_right h' hh.le

/-- **Cellwise matching.**  If in every cell the sources are no more numerous than the targets, one
injection sends every source to a target of its own cell. -/
theorem exists_cellwise_injOn (c : ℕ → ℕ) (s t : Finset ℕ)
    (h : ∀ i, (s.filter (c · = i)).card ≤ (t.filter (c · = i)).card) :
    ∃ f : ℕ → ℕ, Set.InjOn f ↑s ∧ ∀ x ∈ s, f x ∈ t ∧ c (f x) = c x := by
  choose g hg using fun i => Sieve.exists_injOn_of_card_le (h i)
  have hmem : ∀ x ∈ s, g (c x) x ∈ t ∧ c (g (c x) x) = c x := fun x hx =>
    mem_filter.mp ((hg (c x)).2 x (mem_filter.mpr ⟨hx, rfl⟩))
  refine ⟨fun x => g (c x) x, fun x hx y hy hxy => ?_, hmem⟩
  simp only at hxy
  have hc : c x = c y := by
    rw [← (hmem x hx).2, ← (hmem y hy).2, hxy]
  have hx' : x ∈ s.filter (c · = c x) := mem_filter.mpr ⟨hx, rfl⟩
  have hy' : y ∈ s.filter (c · = c x) := mem_filter.mpr ⟨hy, hc.symm⟩
  exact (hg (c x)).1 hx' hy' (by rw [hc] at hxy ⊢; exact hxy)

/-- `J = ⌊(log R)^B⌋` cells of width `h = R/J` satisfy `R/(log R)^B ≤ h ≤ 2R/(log R)^B`. -/
theorem cell_scale {R x : ℝ} (hR : 0 < R) (hx : 1 ≤ x) :
    1 ≤ ⌊x⌋₊ ∧ R / x ≤ R / ⌊x⌋₊ ∧ R / ⌊x⌋₊ ≤ 2 * R / x ∧ (⌊x⌋₊ : ℝ) * (R / ⌊x⌋₊) = R := by
  have hJ1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hJ0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hJ1
  have hJx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hx2 : x ≤ 2 * ⌊x⌋₊ := by
    have := Nat.lt_floor_add_one x
    have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hJ1
    linarith
  refine ⟨hJ1, div_le_div_of_nonneg_left hR.le hJ0 hJx, ?_, by field_simp⟩
  rw [div_le_div_iff₀ hJ0 (by linarith)]
  nlinarith

/-- **Band Lipschitz law.**  For `x, y ∈ [R, 2R]`: `‖f_y - f_x‖_δ ≤ 4 C_1 |y - x| R^{-(3+δ)/2}`. -/
theorem gammaNorm_atom_sub_band {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {R x y : ℝ} (hR : 0 < R)
    (hx : R ≤ x) (hx2 : x ≤ 2 * R) (hy : R ≤ y) (hy2 : y ≤ 2 * R) :
    gammaNorm δ (fun t => atom y t - atom x t) ≤ 4 * jetConst 1 * |y - x| * R ^ (-(3 + δ) / 2) := by
  have key : ∀ a b : ℝ, R ≤ a → a ≤ b → b ≤ 2 * R →
      gammaNorm δ (fun t => atom b t - atom a t) ≤ 4 * jetConst 1 * (b - a) * R ^ (-(3 + δ) / 2) := by
    intro a b hRa hab hb
    have ha : 0 < a := hR.trans_le hRa
    refine (gammaNorm_atom_sub_le hδ0 hδ1 ha hab).trans ?_
    have hC := jetConst_nonneg 1
    have e : (a ^ ((5 + δ) / 2))⁻¹ / a = a ^ (-(7 + δ) / 2) := by
      rw [← Real.rpow_neg ha.le, div_eq_mul_inv, ← Real.rpow_neg_one a, ← Real.rpow_add ha]
      ring_nf
    have hb2 : b ^ 2 ≤ 4 * R ^ 2 := by nlinarith
    have hpow : a ^ (-(7 + δ) / 2) ≤ R ^ (-(7 + δ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hR hRa (by linarith)
    have eR : R ^ 2 * R ^ (-(7 + δ) / 2) = R ^ (-(3 + δ) / 2) := by
      rw [← Real.rpow_two, ← Real.rpow_add hR]; ring_nf
    have hba : 0 ≤ b - a := by linarith
    calc (b - a) * (jetConst 1 * b ^ 2 * (a ^ ((5 + δ) / 2))⁻¹ / a)
        = (b - a) * jetConst 1 * b ^ 2 * ((a ^ ((5 + δ) / 2))⁻¹ / a) := by ring
      _ = (b - a) * jetConst 1 * b ^ 2 * a ^ (-(7 + δ) / 2) := by rw [e]
      _ ≤ (b - a) * jetConst 1 * (4 * R ^ 2) * R ^ (-(7 + δ) / 2) := by gcongr
      _ = 4 * jetConst 1 * (b - a) * (R ^ 2 * R ^ (-(7 + δ) / 2)) := by ring
      _ = 4 * jetConst 1 * (b - a) * R ^ (-(3 + δ) / 2) := by rw [eR]
  rcases le_total x y with hxy | hxy
  · rw [abs_of_nonneg (by linarith)]
    exact key x y hx hxy hy2
  · have hδ : 0 < 5 + δ := by linarith
    have hfin : GammaFinite δ (fun t => atom x t - atom y t) :=
      (gammaFinite_atom hδ (by linarith)).sub (gammaFinite_atom hδ (by linarith))
    have e : (fun t => atom y t - atom x t) = fun t => -(atom x t - atom y t) := by
      funext t; ring
    rw [e, gammaNorm_neg hδ hfin, abs_of_nonpos (by linarith), neg_sub]
    exact key y x hy hxy hx2

/-- **Exact derivative energy.**  `‖∂_x f_x‖_δ² = (δ² + 3δ + 6) 2^{-(7+δ)} x^{-3-δ}`: with
`∂_x f_x = 2x e^{-xt} - x² t e^{-xt}` and the Gram law
`⟨t^j e^{-xt}, t^k e^{-xt}⟩_δ = Γ(5+δ+j+k)/(Γ(5+δ)(2x)^{5+δ+j+k})`. -/
theorem gammaEnergy_atomJet_one {δ : ℝ} (hδ : 0 < 5 + δ) {x : ℝ} (hx : 0 < x) :
    gammaEnergy δ (atomJet 1 x) = (δ ^ 2 + 3 * δ + 6) / 2 ^ (7 + δ) * x ^ (-3 - δ) := by
  have e : atomJet 1 x = fun t => 2 * x * expMono 0 x t - x ^ 2 * expMono 1 x t := by
    funext t; simp [atomJet, expMono]; ring
  have h0 := gammaFinite_expMono hδ 0 hx
  have h1 := gammaFinite_expMono hδ 1 hx
  rw [e, gammaEnergy_sub hδ (h0.smul _) (h1.smul _), gammaEnergy, gammaEnergy,
    gammaInner_smul_left hδ h0 (h0.smul _), gammaInner_smul_right hδ h0 h0,
    gammaInner_smul_left hδ h0 (h1.smul _), gammaInner_smul_right hδ h1 h0,
    gammaInner_smul_left hδ h1 (h1.smul _), gammaInner_smul_right hδ h1 h1,
    gammaInner_expMono hδ 0 0 hx hx, gammaInner_expMono hδ 0 1 hx hx,
    gammaInner_expMono hδ 1 1 hx hx]
  have hG0 : Real.Gamma (5 + δ) ≠ 0 := (gamma_pos hδ).ne'
  have hG1 : Real.Gamma (5 + δ + ((0 + 1 : ℕ) : ℝ)) = (5 + δ) * Real.Gamma (5 + δ) := by
    push_cast; rw [Real.Gamma_add_one (by linarith)]
  have hG2 : Real.Gamma (5 + δ + ((1 + 1 : ℕ) : ℝ)) = (6 + δ) * (5 + δ) * Real.Gamma (5 + δ) := by
    push_cast
    rw [show (5 : ℝ) + δ + 2 = (6 + δ) + 1 by ring, Real.Gamma_add_one (by linarith),
      show (6 : ℝ) + δ = (5 + δ) + 1 by ring, Real.Gamma_add_one (by linarith)]
    ring
  have hx2 : (0 : ℝ) < x + x := by linarith
  have ep : ∀ k : ℕ, (x + x) ^ (5 + δ + (k : ℝ)) = 2 ^ (5 + δ) * x ^ (5 + δ) * (2 * x) ^ k := by
    intro k
    rw [Real.rpow_add hx2, show x + x = 2 * x by ring, Real.mul_rpow (by norm_num) hx.le,
      Real.rpow_natCast]
  have ex : x ^ (-3 - δ) = x ^ 2 / x ^ (5 + δ) := by
    rw [show (-3 : ℝ) - δ = 2 - (5 + δ) by ring, Real.rpow_sub hx, Real.rpow_two]
  have e2 : (2 : ℝ) ^ (7 + δ) = 4 * 2 ^ (5 + δ) := by
    rw [show (7 : ℝ) + δ = 2 + (5 + δ) by ring, Real.rpow_add (by norm_num)]; norm_num
  rw [hG1, hG2, ex, e2]
  simp only [add_zero, show ((0 + 0 : ℕ) : ℝ) = 0 by norm_num]
  rw [show (0 + 1 : ℕ) = 1 by rfl, show (1 + 1 : ℕ) = 2 by rfl, ep 1, ep 2]
  have hx5 : (0 : ℝ) < x ^ (5 + δ) := Real.rpow_pos_of_pos hx _
  have hx5' : (0 : ℝ) < (x + x) ^ (5 + δ) := Real.rpow_pos_of_pos hx2 _
  rw [show (x + x) ^ (5 + δ) = 2 ^ (5 + δ) * x ^ (5 + δ) by
    rw [show x + x = 2 * x by ring, Real.mul_rpow (by norm_num) hx.le]]
  have h25 : (0 : ℝ) < 2 ^ (5 + δ) := by positivity
  field_simp
  ring

/-- The derivative energy constant `(δ² + 3δ + 6) 2^{-(7+δ)}` is continuous in `δ`. -/
theorem continuous_derivEnergyConst :
    Continuous fun δ : ℝ => (δ ^ 2 + 3 * δ + 6) / 2 ^ (7 + δ) :=
  (by fun_prop : Continuous fun δ : ℝ => δ ^ 2 + 3 * δ + 6).div
    (continuous_const.rpow (continuous_const.add continuous_id) fun _ => Or.inl two_ne_zero)
    fun δ => (Real.rpow_pos_of_pos (by norm_num) _).ne'

/-- The derivative energy constant is at most `10/128` for `0 ≤ δ ≤ 1`. -/
theorem derivEnergyConst_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (δ ^ 2 + 3 * δ + 6) / 2 ^ (7 + δ) ≤ 10 / 128 := by
  have h2 : (128 : ℝ) ≤ 2 ^ (7 + δ) := by
    calc (128 : ℝ) = 2 ^ (7 : ℝ) := by norm_num
      _ ≤ 2 ^ (7 + δ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  nlinarith

/-- **Literal dipoles.**  A matched family `p ↦ φ(p)` with `μ(p) = -s`, `μ(φ(p)) = s`, `φ` injective
and image disjoint from the sources, is the literal Möbius subsum over sources and targets. -/
theorem sum_dipoles_eq_literal (P : Finset ℕ) (φ : ℕ → ℕ) (s : ℤ) (hinj : Set.InjOn φ ↑P)
    (hdisj : Disjoint P (P.image φ)) (hμ : ∀ p ∈ P, μ p = -s ∧ μ (φ p) = s) (t : ℝ) :
    ∑ p ∈ P, (s : ℝ) * (atom (φ p) t - atom p t) =
      ∑ n ∈ P ∪ P.image φ, ((μ n : ℤ) : ℝ) * atom n t := by
  rw [sum_union hdisj, sum_image hinj, ← sum_add_distrib]
  refine sum_congr rfl fun p hp => ?_
  rw [(hμ p hp).1, (hμ p hp).2]
  push_cast
  ring

/-- **Norm of a matched family.**  If every source and target lies in `[R, 2R]` and every pair is at
distance at most `D`, the matched family has norm at most `#P · 4 C_1 D R^{-(3+δ)/2}`. -/
theorem gammaNorm_matched_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {R D : ℝ} (hR : 0 < R)
    (P : Finset ℕ) (φ : ℕ → ℕ) (hP : ∀ p ∈ P, R ≤ p ∧ (p : ℝ) ≤ 2 * R)
    (hφ : ∀ p ∈ P, R ≤ φ p ∧ (φ p : ℝ) ≤ 2 * R) (hD : ∀ p ∈ P, |(φ p : ℝ) - p| ≤ D) :
    gammaNorm δ (fun t => ∑ p ∈ P, (atom (φ p) t - atom p t)) ≤
      P.card * (4 * jetConst 1 * D * R ^ (-(3 + δ) / 2)) := by
  have hδ : 0 < 5 + δ := by linarith
  have hfin : ∀ p ∈ P, GammaFinite δ (fun t => atom (φ p) t - atom p t) := fun p hp =>
    (gammaFinite_atom hδ (by linarith [(hφ p hp).1])).sub (gammaFinite_atom hδ (by linarith [(hP p hp).1]))
  refine (gammaNorm_sum_le hδ P hfin).trans ?_
  rw [← nsmul_eq_mul]
  refine sum_le_card_nsmul P _ _ fun p hp => ?_
  have hC := jetConst_nonneg 1
  refine (gammaNorm_atom_sub_band hδ0 hδ1 hR (hP p hp).1 (hP p hp).2 (hφ p hp).1 (hφ p hp).2).trans ?_
  have := Real.rpow_nonneg hR.le (-(3 + δ) / 2)
  gcongr
  exact hD p hp

end RHTower.PrimeCells
