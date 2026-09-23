/-
# The Lorentzian coarse-graining energy of a finite mass configuration

For masses `m_j ≥ 0` at real positions `d_j` and a resolution `a ≠ 0`, the Lorentzian energy is

`E_a = ∑_{j,k} m_j m_k · a² / (a² + (d_j - d_k)²)`.

It is the energy of the measure `∑ m_j δ_{d_j}` against the Poisson kernel of width `a`, and it
arises as `h · ∮ |Ξ'/Ξ|²` on the vertical edges of a slab of half-height `h`, at `a = 2h`, where
`d_j` are the displacements of the zeros in the height fiber from the critical line.

The results below are the algebra of that energy:

* `poissonEnergy_le_sq_sum` — `E_a ≤ M²` at every resolution, `M = ∑ m_j` the total mass;
* `poissonEnergy_eq_sq_sum_iff` — equality holds at one resolution **iff** all positions coincide,
  so the ceiling is attained without passing to a limit;
* `sum_sq_le_poissonEnergy` — `E_a` dominates the second moment `∑ m_j²`;
* `poissonEnergy_mono` — `E_a` increases with the resolution, interpolating between `∑ m_j²` and
  `M²`;
* `eq_zero_of_const_of_mirror` — under a mass-preserving reflection `d ↦ -d` of the configuration,
  constant position forces zero position.
-/
import Mathlib

namespace GaloisForLFunctions
namespace RHTower
namespace PoissonCoarseGrainingEnergy

variable {ι : Type*}

/-! ### The Lorentzian kernel -/

/-- The Lorentzian kernel at resolution `a` and separation `x`. -/
noncomputable def lorentz (a x : ℝ) : ℝ := a ^ (2 : ℕ) / (a ^ (2 : ℕ) + x ^ (2 : ℕ))

lemma lorentz_denom_pos {a : ℝ} (ha : a ≠ 0) (x : ℝ) : 0 < a ^ (2 : ℕ) + x ^ (2 : ℕ) := by
  have h : 0 < a ^ (2 : ℕ) := by positivity
  nlinarith [sq_nonneg x]

lemma lorentz_nonneg {a : ℝ} (ha : a ≠ 0) (x : ℝ) : 0 ≤ lorentz a x := by
  have := lorentz_denom_pos ha x
  unfold lorentz
  positivity

lemma lorentz_le_one {a : ℝ} (ha : a ≠ 0) (x : ℝ) : lorentz a x ≤ 1 := by
  have hd := lorentz_denom_pos ha x
  unfold lorentz
  rw [div_le_one hd]
  nlinarith [sq_nonneg x]

lemma lorentz_self {a : ℝ} (ha : a ≠ 0) : lorentz a 0 = 1 := by
  have h : 0 < a ^ (2 : ℕ) := by positivity
  unfold lorentz
  rw [show (0:ℝ) ^ (2 : ℕ) = 0 by ring, add_zero]
  exact div_self (ne_of_gt h)

lemma lorentz_eq_one_iff {a : ℝ} (ha : a ≠ 0) (x : ℝ) : lorentz a x = 1 ↔ x = 0 := by
  have hd := lorentz_denom_pos ha x
  constructor
  · intro h
    unfold lorentz at h
    rw [div_eq_one_iff_eq (ne_of_gt hd)] at h
    have hx : x ^ (2 : ℕ) = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hx
  · intro h
    rw [h]
    exact lorentz_self ha

/-- The kernel increases with the resolution: coarser scales see more correlation. -/
lemma lorentz_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    lorentz a x ≤ lorentz b x := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hb' : b ≠ 0 := ne_of_gt hb
  have hda := lorentz_denom_pos ha' x
  have hdb := lorentz_denom_pos hb' x
  have key : lorentz b x - lorentz a x
      = (x ^ (2 : ℕ) * (b ^ (2 : ℕ) - a ^ (2 : ℕ))) / ((b ^ (2 : ℕ) + x ^ (2 : ℕ)) * (a ^ (2 : ℕ) + x ^ (2 : ℕ))) := by
    unfold lorentz
    field_simp
    ring
  have hba : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ) := by nlinarith
  have hnum : 0 ≤ x ^ (2 : ℕ) * (b ^ (2 : ℕ) - a ^ (2 : ℕ)) := mul_nonneg (sq_nonneg x) (by linarith)
  have hden : 0 < (b ^ (2 : ℕ) + x ^ (2 : ℕ)) * (a ^ (2 : ℕ) + x ^ (2 : ℕ)) := mul_pos hdb hda
  have : 0 ≤ lorentz b x - lorentz a x := by
    rw [key]
    exact div_nonneg hnum hden.le
  linarith

/-! ### The coarse-graining energy -/

/-- The Lorentzian coarse-graining energy of a fiber with masses `m` and displacements `d`,
at resolution `a`. -/
noncomputable def poissonEnergy (s : Finset ι) (m d : ι → ℝ) (a : ℝ) : ℝ :=
  ∑ j ∈ s, ∑ k ∈ s, m j * m k * lorentz a (d j - d k)

/-- **Upper bound: the energy never exceeds the squared fiber mass.** -/
theorem poissonEnergy_le_sq_sum (s : Finset ι) (m d : ι → ℝ) {a : ℝ} (ha : a ≠ 0)
    (hm : ∀ j ∈ s, 0 ≤ m j) :
    poissonEnergy s m d a ≤ (∑ j ∈ s, m j) ^ (2 : ℕ) := by
  have hexp : (∑ j ∈ s, m j) ^ (2 : ℕ) = ∑ j ∈ s, ∑ k ∈ s, m j * m k := by
    rw [sq, Finset.sum_mul_sum]
  rw [hexp, poissonEnergy]
  refine Finset.sum_le_sum ?_
  intro j hj
  refine Finset.sum_le_sum ?_
  intro k hk
  have hmm : 0 ≤ m j * m k := mul_nonneg (hm j hj) (hm k hk)
  calc m j * m k * lorentz a (d j - d k) ≤ m j * m k * 1 :=
        mul_le_mul_of_nonneg_left (lorentz_le_one ha _) hmm
    _ = m j * m k := by ring

/-- **The limit-free certificate.**  With positive masses the energy attains its ceiling `M²` at
one resolution iff every displacement coincides — no `h → 0` germ is required. -/
theorem poissonEnergy_eq_sq_sum_iff (s : Finset ι) (m d : ι → ℝ) {a : ℝ} (ha : a ≠ 0)
    (hm : ∀ j ∈ s, 0 < m j) :
    poissonEnergy s m d a = (∑ j ∈ s, m j) ^ (2 : ℕ) ↔ ∀ j ∈ s, ∀ k ∈ s, d j = d k := by
  have hexp : (∑ j ∈ s, m j) ^ (2 : ℕ) = ∑ j ∈ s, ∑ k ∈ s, m j * m k := by
    rw [sq, Finset.sum_mul_sum]
  rw [poissonEnergy]
  constructor
  · intro h j hj k hk
    -- the deficit is a sum of nonnegative terms which vanishes
    have hdef : ∑ j ∈ s, ∑ k ∈ s, (m j * m k - m j * m k * lorentz a (d j - d k)) = 0 := by
      simp only [Finset.sum_sub_distrib]
      rw [← hexp, h]
      ring
    have hnn : ∀ i ∈ s, 0 ≤ ∑ k ∈ s, (m i * m k - m i * m k * lorentz a (d i - d k)) := by
      intro i hi
      refine Finset.sum_nonneg ?_
      intro k hk
      have hmm : 0 ≤ m i * m k := mul_nonneg (hm i hi).le (hm k hk).le
      nlinarith [lorentz_le_one ha (d i - d k), lorentz_nonneg ha (d i - d k)]
    have hrow := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hdef j hj
    have hnn' : ∀ k ∈ s, 0 ≤ m j * m k - m j * m k * lorentz a (d j - d k) := by
      intro k hk
      have hmm : 0 ≤ m j * m k := mul_nonneg (hm j hj).le (hm k hk).le
      nlinarith [lorentz_le_one ha (d j - d k), lorentz_nonneg ha (d j - d k)]
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn').mp hrow k hk
    have hmm : 0 < m j * m k := mul_pos (hm j hj) (hm k hk)
    have hL : lorentz a (d j - d k) = 1 := by
      have : m j * m k * (1 - lorentz a (d j - d k)) = 0 := by linarith [hterm]
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 (ne_of_gt hmm)
      · linarith
    have := (lorentz_eq_one_iff ha (d j - d k)).mp hL
    linarith
  · intro h
    rw [hexp]
    refine Finset.sum_congr rfl ?_
    intro j hj
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hd : d j - d k = 0 := by rw [h j hj k hk]; ring
    rw [hd, lorentz_self ha]
    ring

/-- **Lower bound: the energy dominates the multiplicity second moment.** -/
theorem sum_sq_le_poissonEnergy (s : Finset ι) (m d : ι → ℝ) {a : ℝ} (ha : a ≠ 0)
    (hm : ∀ j ∈ s, 0 ≤ m j) :
    ∑ j ∈ s, (m j) ^ (2 : ℕ) ≤ poissonEnergy s m d a := by
  rw [poissonEnergy]
  refine Finset.sum_le_sum ?_
  intro j hj
  have hdiag : m j * m j * lorentz a (d j - d j) = (m j) ^ (2 : ℕ) := by
    rw [show d j - d j = 0 by ring, lorentz_self ha]
    ring
  have hnn : ∀ k ∈ s, 0 ≤ m j * m k * lorentz a (d j - d k) := by
    intro k hk
    exact mul_nonneg (mul_nonneg (hm j hj) (hm k hk)) (lorentz_nonneg ha _)
  calc (m j) ^ (2 : ℕ) = m j * m j * lorentz a (d j - d j) := hdiag.symm
    _ ≤ ∑ k ∈ s, m j * m k * lorentz a (d j - d k) := Finset.single_le_sum hnn hj

/-- **The coarse-graining flow is monotone in the resolution.** -/
theorem poissonEnergy_mono (s : Finset ι) (m d : ι → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hm : ∀ j ∈ s, 0 ≤ m j) :
    poissonEnergy s m d a ≤ poissonEnergy s m d b := by
  rw [poissonEnergy, poissonEnergy]
  refine Finset.sum_le_sum ?_
  intro j hj
  refine Finset.sum_le_sum ?_
  intro k hk
  exact mul_le_mul_of_nonneg_left (lorentz_mono ha hab _)
    (mul_nonneg (hm j hj) (hm k hk))

/-! ### The mirror step -/

/-- **The functional equation upgrades constancy to vanishing.**  On a fiber invariant under the
mass-preserving reflection `d ↦ -d`, constant displacement forces zero displacement. -/
theorem eq_zero_of_const_of_mirror (s : Finset ι) (d : ι → ℝ) (σ : ι → ι)
    (hmem : ∀ a ∈ s, σ a ∈ s) (hd : ∀ a ∈ s, d (σ a) = - d a)
    (hconst : ∀ j ∈ s, ∀ k ∈ s, d j = d k) :
    ∀ j ∈ s, d j = 0 := by
  intro j hj
  have hσ : σ j ∈ s := hmem j hj
  have h1 : d j = d (σ j) := hconst j hj (σ j) hσ
  have h2 : d (σ j) = - d j := hd j hj
  linarith

/-! ### The exact detection gap of a mirror pair

A configuration of two equal masses `m` at `±d` is compared with the single mass `2 m` at the
origin obtained by merging them.  The coarse-grained energies differ by an explicit amount which
decays in the resolution: at resolution `a` the merged configuration is indistinguishable from the
split one to within `8 m² d² / (a² + 4 d²)`, and half the total signal is visible exactly when
`a ≤ 2 d`.  Detecting a splitting of size `d` therefore requires resolution comparable to `d`. -/

lemma lorentz_neg {a : ℝ} (x : ℝ) : lorentz a (-x) = lorentz a x := by
  unfold lorentz
  ring_nf

/-- The energy of two equal masses `m` at `±d`. -/
theorem poissonEnergy_mirror_pair (m d : ℝ) {a : ℝ} (ha : a ≠ 0) :
    poissonEnergy (Finset.univ : Finset (Fin 2)) (fun _ => m) (![d, -d]) a
      = 2 * m ^ (2 : ℕ) * (1 + lorentz a (2 * d)) := by
  simp only [poissonEnergy, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show d - d = 0 by ring, show -d - -d = 0 by ring, show d - -d = 2 * d by ring,
    show -d - d = -(2 * d) by ring, lorentz_self ha, lorentz_neg]
  ring

/-- The energy of the merged configuration: a single mass `2 m`. -/
theorem poissonEnergy_merged (m : ℝ) {a : ℝ} (ha : a ≠ 0) :
    poissonEnergy (Finset.univ : Finset (Fin 1)) (fun _ => 2 * m) (fun _ => 0) a
      = (2 * m) ^ (2 : ℕ) := by
  simp only [poissonEnergy, Fin.sum_univ_one]
  rw [show (0:ℝ) - 0 = 0 by ring, lorentz_self ha]
  ring

/-- **The exact detection gap.**  Merging a mirror pair at `±d` raises the coarse-grained energy by
exactly `8 m² d² / (a² + 4 d²)`. -/
theorem poissonEnergy_mirror_pair_gap (m d : ℝ) {a : ℝ} (ha : a ≠ 0) :
    (2 * m) ^ (2 : ℕ) - 2 * m ^ (2 : ℕ) * (1 + lorentz a (2 * d))
      = 8 * m ^ (2 : ℕ) * d ^ (2 : ℕ) / (a ^ (2 : ℕ) + 4 * d ^ (2 : ℕ)) := by
  have hd : (0:ℝ) < a ^ (2 : ℕ) + (2 * d) ^ (2 : ℕ) := lorentz_denom_pos ha (2 * d)
  have hd' : a ^ (2 : ℕ) + 4 * d ^ (2 : ℕ) ≠ 0 := by
    intro h
    rw [show a ^ (2 : ℕ) + (2 * d) ^ (2 : ℕ) = a ^ (2 : ℕ) + 4 * d ^ (2 : ℕ) by ring] at hd
    exact absurd h (ne_of_gt hd)
  unfold lorentz
  field_simp
  ring

/-- **The resolution threshold.**  At least half the merged energy of the pair is visible at
resolution `a` exactly when `a ≤ 2 d`: a splitting of size `d` cannot be detected at any coarser
resolution. -/
theorem poissonEnergy_gap_ge_iff (m d : ℝ) {a : ℝ} (ha : a ≠ 0) (hm : m ≠ 0) (_hd : d ≠ 0) :
    m ^ (2 : ℕ) ≤ 8 * m ^ (2 : ℕ) * d ^ (2 : ℕ) / (a ^ (2 : ℕ) + 4 * d ^ (2 : ℕ)) ↔ a ^ (2 : ℕ) ≤ 4 * d ^ (2 : ℕ) := by
  have hpos : (0:ℝ) < a ^ (2 : ℕ) + 4 * d ^ (2 : ℕ) := by
    have h1 : 0 < a ^ (2 : ℕ) := by positivity
    nlinarith [sq_nonneg d]
  have hm2 : 0 < m ^ (2 : ℕ) := by positivity
  rw [le_div_iff₀ hpos]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

end PoissonCoarseGrainingEnergy
end RHTower
end GaloisForLFunctions

