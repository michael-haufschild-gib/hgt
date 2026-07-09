/-
# The global vertical clock of a zero set and its trichotomy

For a set `Z ⊆ ℂ`, the **vertical stabilizer** `vStab Z` is the set of real vertical translation
periods `t` under which `Z` is invariant, `(fun z => z + t·i) '' Z = Z`, encoded in the iff form
`∀ z, z ∈ Z ↔ z + t·i ∈ Z`.  It is an additive subgroup of `ℝ`, closed when `Z` is closed — the
*global vertical clock* of `Z`.

By the classification of additive subgroups of `ℝ` (`AddSubgroup.dense_or_cyclic`), such a subgroup
is either dense or cyclic.  For the zero set of an entire function that is not identically zero,
density is impossible: a dense subgroup contains nonzero elements arbitrarily close to `0`, so the
translates of any one zero accumulate at that zero, and by the identity principle on the connected
plane the function would vanish everywhere.  Hence the stabilizer is cyclic, `{0}` or a lattice
`αℤ`: a nonzero entire carrier has either **no** global vertical clock or exactly one primitive one.

**Separation from pointwise periodicity.**  Every zero of a single prime column
`1 − c·b^{−s}` lies on a vertical arithmetic progression of period `2π/log b`, so its zeros are
individually clockwork.  A two-prime product `twoClock s = (1 − 2·2^{−s})(1 − 9·3^{−s})` inherits
this pointwise periodicity — each zero propagates along the period of the column that produced it —
yet its global stabilizer is trivial.  A common vertical period `t` would send the base-2 zero at
`s = 1` back into the base-2 lattice (`t ∈ (2π/log 2)ℤ`) and the base-3 zero at `s = 2` back into the
base-3 lattice (`t ∈ (2π/log 3)ℤ`); a nonzero common value forces `a·log 3 = b·log 2` with `a, b`
nonzero integers, i.e. `3^{|a|} = 2^{|b|}`, impossible by parity.  The irrationality of the rate
lattice `⟨log 2, log 3⟩` shatters global symmetry into per-column clocks: on a multi-prime carrier it
is the pointwise (per-zero) period, not the global stabilizer, that survives as the invariant.
-/
import GaloisForLFunctions.RHTower.DAColumnDivisor
import GaloisForLFunctions.RHTower.DegreeZeroOffline
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Algebra.Order.Archimedean

noncomputable section

namespace RHTower

open Complex Filter Topology

/-- The **vertical stabilizer** of a set `Z ⊆ ℂ`: the additive subgroup of real vertical periods `t`
for which `Z` is invariant under `z ↦ z + t·i`, written in iff form `∀ z, z ∈ Z ↔ z + t·i ∈ Z`.
The group axioms are immediate: the iff composes (add), inverts (neg) — applying the iff at the
translated point `z + (-t)·i` gives back `z` — and is reflexive at `t = 0`. -/
def vStab (Z : Set ℂ) : AddSubgroup ℝ where
  carrier := {t : ℝ | ∀ z : ℂ, z ∈ Z ↔ z + (t : ℂ) * Complex.I ∈ Z}
  zero_mem' := by intro z; simp
  add_mem' := by
    intro a b ha hb z
    rw [ha z, hb (z + (a : ℂ) * Complex.I)]
    have he : z + (a : ℂ) * Complex.I + (b : ℂ) * Complex.I
        = z + ((a + b : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he]
  neg_mem' := by
    intro a ha z
    have h := ha (z + ((-a : ℝ) : ℂ) * Complex.I)
    have he : z + ((-a : ℝ) : ℂ) * Complex.I + (a : ℂ) * Complex.I = z := by push_cast; ring
    rw [he] at h
    exact h.symm

/-- Membership in the vertical stabilizer unfolds to the invariance iff. -/
theorem mem_vStab {Z : Set ℂ} {t : ℝ} :
    t ∈ vStab Z ↔ ∀ z : ℂ, (z ∈ Z ↔ z + (t : ℂ) * Complex.I ∈ Z) := Iff.rfl

/-- **The stabilizer of a closed set is closed.**  Given `tₙ → t` with each `tₙ` stabilizing `Z`:
for `z ∈ Z` the translates `z + tₙ·i ∈ Z` converge to `z + t·i`, closed in `Z`; for the reverse
inclusion apply the stabilizer at the point `z + t·i` with periods `-tₙ`, so `z + (t − tₙ)·i ∈ Z`
converge to `z`, again closed in `Z`.  The iff form supplies both directions pointwise. -/
theorem vStab_isClosed {Z : Set ℂ} (hZ : IsClosed Z) : IsClosed (vStab Z : Set ℝ) := by
  apply IsSeqClosed.isClosed
  intro x t hx htend
  rw [SetLike.mem_coe, mem_vStab]
  intro z
  have hcont : Continuous (fun r : ℝ => z + (r : ℂ) * Complex.I) := by fun_prop
  constructor
  · intro hz
    have hmem : ∀ n, z + ((x n : ℝ) : ℂ) * Complex.I ∈ Z := fun n => ((hx n) z).mp hz
    have htend2 : Tendsto (fun n => z + ((x n : ℝ) : ℂ) * Complex.I) atTop
        (𝓝 (z + (t : ℂ) * Complex.I)) := (hcont.tendsto t).comp htend
    exact hZ.mem_of_tendsto htend2 (Eventually.of_forall hmem)
  · intro hw
    have hmem : ∀ n, z + ((t - x n : ℝ) : ℂ) * Complex.I ∈ Z := by
      intro n
      have h := (hx n) (z + ((t - x n : ℝ) : ℂ) * Complex.I)
      have he : z + ((t - x n : ℝ) : ℂ) * Complex.I + ((x n : ℝ) : ℂ) * Complex.I
          = z + (t : ℂ) * Complex.I := by push_cast; ring
      rw [he] at h
      exact h.mpr hw
    have htend0 : Tendsto (fun n => t - x n) atTop (𝓝 (t - t)) := tendsto_const_nhds.sub htend
    have htend2 : Tendsto (fun n => z + ((t - x n : ℝ) : ℂ) * Complex.I) atTop
        (𝓝 (z + ((t - t : ℝ) : ℂ) * Complex.I)) := (hcont.tendsto (t - t)).comp htend0
    rw [sub_self] at htend2
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at htend2
    exact hZ.mem_of_tendsto htend2 (Eventually.of_forall hmem)

/-- **Trichotomy collapse for analytic carriers.**  The vertical stabilizer of the zero set of an
entire function that is not identically zero is cyclic: `vStab {F = 0} = ⟨a⟩` for some `a`.  By
`AddSubgroup.dense_or_cyclic` the stabilizer is dense or cyclic.  In the dense branch, choosing a zero
`s₀` and translating it by stabilizer elements in `(0, ε)` produces zeros of `F` distinct from `s₀`
and within `ε` of it, so `s₀` lies in the closure of `{F = 0} \ {s₀}`; the identity principle on the
connected plane then forces `F ≡ 0`, contradicting `hne`.  Hence only the cyclic branch survives. -/
theorem vStab_cyclic_of_analytic {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ)
    (hne : ∃ s, F s ≠ 0) (hz : ∃ s, F s = 0) :
    ∃ a : ℝ, vStab {s | F s = 0} = AddSubgroup.closure {a} := by
  rcases (vStab {s | F s = 0}).dense_or_cyclic with hdense | hcyc
  · exfalso
    obtain ⟨s₀, hs₀⟩ := hz
    have hmemcl : s₀ ∈ closure ({z | F z = 0} \ {s₀}) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      rw [dense_iff_inter_open] at hdense
      obtain ⟨τ, hτmem, hτstab⟩ := hdense (Set.Ioo 0 ε) isOpen_Ioo ⟨ε / 2, by constructor <;> linarith⟩
      have hτpos : 0 < τ := hτmem.1
      have hstab : τ ∈ vStab {s | F s = 0} := hτstab
      rw [mem_vStab] at hstab
      have hzero : F (s₀ + (τ : ℂ) * Complex.I) = 0 := (hstab s₀).mp hs₀
      refine ⟨s₀ + (τ : ℂ) * Complex.I, ⟨hzero, ?_⟩, ?_⟩
      · simp only [Set.mem_singleton_iff]
        intro hcon
        have h0 : (τ : ℂ) * Complex.I = 0 := by linear_combination hcon
        rw [mul_eq_zero] at h0
        rcases h0 with h | h
        · exact (ne_of_gt hτpos) (by exact_mod_cast h)
        · exact Complex.I_ne_zero h
      · rw [Complex.dist_eq]
        have he : s₀ - (s₀ + (τ : ℂ) * Complex.I) = -((τ : ℂ) * Complex.I) := by ring
        rw [he, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hτpos]
        exact hτmem.2
    have heq := hF.eqOn_zero_of_preconnected_of_mem_closure isPreconnected_univ
      (Set.mem_univ s₀) hmemcl
    obtain ⟨s, hs⟩ := hne
    exact hs (heq (Set.mem_univ s))
  · exact hcyc

/-- Vertical-shift invariance of a prime-base exponential in cast form: `b^{−s}` is unchanged by the
shift `s ↦ s + k·(2π/log b)·i`.  A restatement of `exp_shift_invariant` with the shift coefficient
written as a real number cast into `ℂ`. -/
private theorem base_cpow_vshift {b : ℕ} (hb : 2 ≤ b) (z : ℂ) (k : ℤ) :
    (b : ℂ) ^ (-(z + ((k : ℂ) * ((2 * Real.pi / Real.log b : ℝ) : ℂ)) * Complex.I))
      = (b : ℂ) ^ (-z) := by
  have he : ((k : ℂ) * ((2 * Real.pi / Real.log b : ℝ) : ℂ))
      = (k * (2 * Real.pi / Real.log b)) := by push_cast; ring
  rw [he]
  exact exp_shift_invariant hb z k

/-- **A single prime column has a nontrivial global clock.**  The degree-zero member `dzo`, a product
of factors in the single exponential `8^{−s}`, is invariant under the vertical shift by its column
period `2π/log 8`, so this period stabilizes its zero set (both directions of the iff follow from the
`+t` and `−t` shift invariance of the exponential). -/
theorem dzo_vStab_nontrivial : (2 * Real.pi / Real.log 8) ∈ vStab {s | dzo s = 0} := by
  rw [mem_vStab]
  intro z
  have hshift : (8 : ℂ) ^ (-(z + ((2 * Real.pi / Real.log 8 : ℝ) : ℂ) * Complex.I))
      = (8 : ℂ) ^ (-z) := by
    have h := base_cpow_vshift (b := 8) (by norm_num) z 1
    rw [show ((8 : ℕ) : ℂ) = (8 : ℂ) by norm_num] at h
    rw [← h]; congr 2; push_cast; ring
  have hval : dzo (z + ((2 * Real.pi / Real.log 8 : ℝ) : ℂ) * Complex.I) = dzo z := by
    simp only [dzo]; rw [hshift]
  simp only [Set.mem_setOf_eq]
  rw [hval]

/-- The two-prime column product `(1 − 2·2^{−s})(1 − 9·3^{−s})`: the first factor vanishes on the
base-2 lattice `Re s = 1`, the second on the base-3 lattice `Re s = 2`. -/
def twoClock : ℂ → ℂ := fun s => (1 - 2 * (2 : ℂ) ^ (-s)) * (1 - 9 * (3 : ℂ) ^ (-s))

/-- **Every zero of `twoClock` is pointwise periodic.**  A zero makes one column factor vanish; that
factor depends on `s` only through its prime exponential and so is invariant under the corresponding
column period `T` (`2π/log 2` or `2π/log 3`), hence the zero repeats along the entire vertical
progression `s₀ + k·T·i`. -/
theorem twoClock_pointwise_periodic (s₀ : ℂ) (h0 : twoClock s₀ = 0) :
    ∃ T : ℝ, 0 < T ∧ ∀ k : ℤ, twoClock (s₀ + ((k : ℂ) * (T : ℂ)) * Complex.I) = 0 := by
  rw [twoClock, mul_eq_zero] at h0
  rcases h0 with hf1 | hf2
  · refine ⟨2 * Real.pi / Real.log 2, div_pos (by positivity) (Real.log_pos (by norm_num)), ?_⟩
    intro k
    rw [twoClock, mul_eq_zero]; left
    have hshift : (2 : ℂ) ^ (-(s₀ + ((k : ℂ) * ((2 * Real.pi / Real.log 2 : ℝ) : ℂ)) * Complex.I))
        = (2 : ℂ) ^ (-s₀) := by
      have h := base_cpow_vshift (b := 2) (by norm_num) s₀ k
      rwa [show ((2 : ℕ) : ℂ) = (2 : ℂ) by norm_num] at h
    rw [hshift]; exact hf1
  · refine ⟨2 * Real.pi / Real.log 3, div_pos (by positivity) (Real.log_pos (by norm_num)), ?_⟩
    intro k
    rw [twoClock, mul_eq_zero]; right
    have hshift : (3 : ℂ) ^ (-(s₀ + ((k : ℂ) * ((2 * Real.pi / Real.log 3 : ℝ) : ℂ)) * Complex.I))
        = (3 : ℂ) ^ (-s₀) := by
      have h := base_cpow_vshift (b := 3) (by norm_num) s₀ k
      rwa [show ((3 : ℕ) : ℂ) = (3 : ℂ) by norm_num] at h
    rw [hshift]; exact hf2

/-- Phase extraction.  If `b^{−t·i} = 1` for a prime base `b ≥ 2`, then `t·log b` is an integer
multiple of `2π`.  Writing `b^{−t·i} = exp(log b · (−t·i))` and applying `exp_eq_one_iff`, the
imaginary part of the resulting equation reads `−(log b·t) = 2π·n`. -/
private theorem phase_extract {b : ℕ} (hb : 2 ≤ b) {t : ℝ}
    (h : (b : ℂ) ^ (-((t : ℂ) * Complex.I)) = 1) :
    ∃ n : ℤ, t * Real.log b = n * (2 * Real.pi) := by
  have hb0 : (b : ℂ) ≠ 0 := by
    have : 0 < b := by omega
    exact_mod_cast this.ne'
  have hbR : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have hlog : Complex.log (b : ℂ) = ((Real.log b : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast b, ← Complex.ofReal_log hbR]
  rw [Complex.cpow_def_of_ne_zero hb0, hlog, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨-n, ?_⟩
  have him := congrArg Complex.im hn
  simp only [Complex.mul_im, Complex.mul_re, Complex.neg_im, Complex.neg_re,
    Complex.ofReal_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
    Complex.intCast_im, Complex.intCast_re, Complex.re_ofNat, Complex.im_ofNat] at him
  push_cast
  nlinarith [him, Real.pi_pos]

/-- Modulus reading of a vanishing column factor.  If `1 − c·b^{−s} = 0` with `c, b > 0` real, then
`c·b^{−Re s} = 1`, since `|b^{−s}| = b^{−Re s}` and `|c| = c`.  Used to fix the real part of any zero
of the factor and to exclude the wrong prime factor at a mismatched real part. -/
private theorem factor_zero_modulus {c b : ℝ} (hc : 0 < c) (hb : 0 < b) {s : ℂ}
    (h : (1 : ℂ) - (c : ℂ) * (b : ℂ) ^ (-s) = 0) :
    c * b ^ (-s.re) = 1 := by
  have h1 : (c : ℂ) * (b : ℂ) ^ (-s) = 1 := by linear_combination -h
  have hnorm := congrArg norm h1
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.norm_real,
    Real.norm_of_nonneg hc.le, Complex.neg_re, norm_one] at hnorm
  exact hnorm

/-- Lattice reading of a vanishing column factor.  If `1 − c·b^{−(σ + t·i)} = 0` and `c·b^{−σ} = 1`
(the modulus constraint at real part `σ`), then splitting `b^{−(σ+t·i)} = b^{−σ}·b^{−t·i}` and
cancelling the real amplitude leaves `b^{−t·i} = 1`, so `phase_extract` gives `t·log b ∈ 2π·ℤ`. -/
private theorem col_stab_lattice {b : ℕ} (hb : 2 ≤ b) {c σ t : ℝ}
    (hcb : c * (b : ℝ) ^ (-σ) = 1)
    (hzero : (1 : ℂ) - (c : ℂ) * (b : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) = 0) :
    ∃ n : ℤ, t * Real.log b = n * (2 * Real.pi) := by
  have hb0 : (b : ℂ) ≠ 0 := by
    have : 0 < b := by omega
    exact_mod_cast this.ne'
  have hbR : (0 : ℝ) ≤ (b : ℝ) := by positivity
  have h1 : (c : ℂ) * (b : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) = 1 := by
    linear_combination -hzero
  have hsplit : (b : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      = (b : ℂ) ^ (-(σ : ℂ)) * (b : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
    rw [← Complex.cpow_add _ _ hb0]; congr 1; ring
  have hsigma : (b : ℂ) ^ (-(σ : ℂ)) = (((b : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hbR, Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [hsplit, hsigma] at h1
  have hcc : (c : ℂ) * (((b : ℝ) ^ (-σ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, hcb, Complex.ofReal_one]
  rw [← mul_assoc, hcc, one_mul] at h1
  exact phase_extract hb h1

/-- `2^B = 3^A` is impossible for `A ≥ 1`: `3^A` is odd, so `2^B` is odd, forcing `B = 0` and then
`3^A = 1`, contradicting `A ≥ 1` (`2 ∣ 2^B` when `B ≥ 1`, but `2 ∤ 3^A`). -/
private theorem two_pow_ne_three_pow {A B : ℕ} (hA : 1 ≤ A) : (2 : ℕ) ^ B ≠ 3 ^ A := by
  intro h
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · rw [hB0, pow_zero, eq_comm, Nat.pow_eq_one] at h
    rcases h with h3 | hA0
    · exact absurd h3 (by decide)
    · omega
  · have hdvd : (2 : ℕ) ∣ 3 ^ A := h ▸ dvd_pow_self 2 (by omega : B ≠ 0)
    exact absurd (Nat.prime_two.dvd_of_dvd_pow hdvd) (by decide)

/-- Incommensurability of `log 2` and `log 3`.  A relation `a·log 3 = b·log 2` with `a ≠ 0` is
impossible: exponentiating gives `3^a = 2^b` in `ℝ` with `a, b` of the same nonzero sign, which
reduces (clearing negative exponents) to `3^{|a|} = 2^{|b|}` in `ℕ`, ruled out by parity. -/
private theorem no_int_log_rel {a b : ℤ} (ha : a ≠ 0)
    (h : (a : ℝ) * Real.log 3 = (b : ℝ) * Real.log 2) : False := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have key : (3 : ℝ) ^ a = (2 : ℝ) ^ b := by
    rw [← Real.rpow_intCast (3 : ℝ) a, ← Real.rpow_intCast (2 : ℝ) b,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [mul_comm (Real.log 3) _, mul_comm (Real.log 2) _, h]
  rcases lt_trichotomy a 0 with hneg | hz | hpos
  · have hbneg : b < 0 := by
      by_contra hbb
      have hbb' : 0 ≤ b := not_lt.mp hbb
      have h1 : (a : ℝ) * Real.log 3 < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hneg) hlog3
      have h2 : 0 ≤ (b : ℝ) * Real.log 2 := mul_nonneg (by exact_mod_cast hbb') hlog2.le
      rw [h] at h1; linarith
    set A := (-a).toNat with hAdef
    set B := (-b).toNat with hBdef
    have hApos : 1 ≤ A := by omega
    have e3 : (3 : ℝ) ^ a = ((3 ^ A : ℕ) : ℝ)⁻¹ := by
      rw [show a = -(A : ℤ) by omega, zpow_neg, zpow_natCast]; push_cast; ring
    have e2 : (2 : ℝ) ^ b = ((2 ^ B : ℕ) : ℝ)⁻¹ := by
      rw [show b = -(B : ℤ) by omega, zpow_neg, zpow_natCast]; push_cast; ring
    rw [e3, e2] at key
    have hnat : ((3 ^ A : ℕ) : ℝ) = ((2 ^ B : ℕ) : ℝ) := inv_inj.mp key
    exact two_pow_ne_three_pow hApos (by exact_mod_cast hnat.symm)
  · exact ha hz
  · have hbpos : 0 < b := by
      by_contra hbb
      have hbb' : b ≤ 0 := not_lt.mp hbb
      have h1 : 0 < (a : ℝ) * Real.log 3 := mul_pos (by exact_mod_cast hpos) hlog3
      have h2 : (b : ℝ) * Real.log 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hbb') hlog2.le
      rw [h] at h1; linarith
    set A := a.toNat with hAdef
    set B := b.toNat with hBdef
    have hApos : 1 ≤ A := by omega
    have e3 : (3 : ℝ) ^ a = ((3 ^ A : ℕ) : ℝ) := by
      rw [show a = (A : ℤ) by omega, zpow_natCast]; push_cast; ring
    have e2 : (2 : ℝ) ^ b = ((2 ^ B : ℕ) : ℝ) := by
      rw [show b = (B : ℤ) by omega, zpow_natCast]; push_cast; ring
    rw [e3, e2] at key
    exact two_pow_ne_three_pow hApos (by exact_mod_cast key.symm)

/-- **The two-prime carrier has trivial global clock.**  `twoClock` is pointwise clockwork yet its
vertical stabilizer is `{0}`.  A stabilizer element `t` carries the base-2 zero `s = 1` back to a
zero: the base-3 factor there has modulus `9·3^{−1} = 3 ≠ 1`, so it is the base-2 factor that
vanishes, forcing `t·log 2 ∈ 2π·ℤ`.  Symmetrically the base-3 zero `s = 2` forces `t·log 3 ∈ 2π·ℤ`.
A common nonzero `t` yields `a·log 3 = b·log 2` with `a, b ≠ 0`, i.e. `3^{|a|} = 2^{|b|}`, impossible;
so `t = 0`. -/
theorem twoClock_vStab_trivial : vStab {s | twoClock s = 0} = ⊥ := by
  rw [AddSubgroup.eq_bot_iff_forall]
  intro t ht
  rw [mem_vStab] at ht
  have h1zero : twoClock (1 : ℂ) = 0 := by
    rw [twoClock, Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_one, Complex.cpow_one]
    norm_num
  have h2zero : twoClock (2 : ℂ) = 0 := by
    rw [twoClock, show (-(2 : ℂ)) = -((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_natCast, Complex.cpow_natCast]
    norm_num
  have h1shift : twoClock ((1 : ℂ) + (t : ℂ) * Complex.I) = 0 := (ht 1).mp h1zero
  have h2shift : twoClock ((2 : ℂ) + (t : ℂ) * Complex.I) = 0 := (ht 2).mp h2zero
  have hlat2 : ∃ n : ℤ, t * Real.log 2 = n * (2 * Real.pi) := by
    rw [twoClock, mul_eq_zero] at h1shift
    rcases h1shift with hf1 | hf2
    · refine col_stab_lattice (b := 2) (by norm_num) (c := 2) (σ := 1) ?_ ?_
      · rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num,
          show (-(1 : ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      · rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num,
          show ((2 : ℕ) : ℂ) = (2 : ℂ) by norm_num, show ((1 : ℝ) : ℂ) = (1 : ℂ) by norm_num]
        exact hf1
    · exfalso
      have hmod := factor_zero_modulus (c := 9) (b := 3) (by norm_num) (by norm_num)
        (by rw [show ((9 : ℝ) : ℂ) = (9 : ℂ) by norm_num,
          show ((3 : ℝ) : ℂ) = (3 : ℂ) by norm_num]; exact hf2)
      rw [show ((1 : ℂ) + (t : ℂ) * Complex.I).re = 1 by simp,
        show (-(1 : ℝ)) = ((-1 : ℤ) : ℝ) by norm_num, Real.rpow_intCast] at hmod
      norm_num at hmod
  have hlat3 : ∃ n : ℤ, t * Real.log 3 = n * (2 * Real.pi) := by
    rw [twoClock, mul_eq_zero] at h2shift
    rcases h2shift with hf1 | hf2
    · exfalso
      have hmod := factor_zero_modulus (c := 2) (b := 2) (by norm_num) (by norm_num)
        (by rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]; exact hf1)
      rw [show ((2 : ℂ) + (t : ℂ) * Complex.I).re = 2 by simp,
        show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast] at hmod
      norm_num at hmod
    · refine col_stab_lattice (b := 3) (by norm_num) (c := 9) (σ := 2) ?_ ?_
      · rw [show ((3 : ℕ) : ℝ) = (3 : ℝ) by norm_num,
          show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
        norm_num
      · rw [show ((9 : ℝ) : ℂ) = (9 : ℂ) by norm_num,
          show ((3 : ℕ) : ℂ) = (3 : ℂ) by norm_num, show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
        exact hf2
  obtain ⟨a, ha2⟩ := hlat2
  obtain ⟨b, hb3⟩ := hlat3
  by_contra ht0
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hane : a ≠ 0 := by
    intro haa
    rw [haa] at ha2
    simp only [Int.cast_zero, zero_mul] at ha2
    rcases mul_eq_zero.mp ha2 with h | h
    · exact ht0 h
    · exact hlog2 h
  have hrel : (a : ℝ) * Real.log 3 = (b : ℝ) * Real.log 2 := by
    have e : ((a : ℝ) * Real.log 3) * (2 * Real.pi) = ((b : ℝ) * Real.log 2) * (2 * Real.pi) := by
      have h' : ((a : ℝ) * (2 * Real.pi)) * Real.log 3
          = ((b : ℝ) * (2 * Real.pi)) * Real.log 2 := by rw [← ha2, ← hb3]; ring
      linear_combination h'
    exact mul_right_cancel₀ h2pi e
  exact no_int_log_rel hane hrel

end RHTower

namespace RHTower

/-- Distinct primes cannot satisfy `q^N = p^M` with positive exponents: `p` divides the
right-hand side, hence divides `q`, hence equals `q`. -/
private lemma prime_pow_log_contra {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {N M : ℕ} (hM : 0 < M)
    (h : (N : ℝ) * Real.log q = (M : ℝ) * Real.log p) : False := by
  have hlq : Real.log ((q : ℝ) ^ N) = Real.log ((p : ℝ) ^ M) := by
    rw [Real.log_pow, Real.log_pow]; exact_mod_cast h
  have hqN : (0 : ℝ) < (q : ℝ) ^ N := by
    have : (0 : ℝ) < q := by exact_mod_cast hq.pos
    positivity
  have hpM : (0 : ℝ) < (p : ℝ) ^ M := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  have heq : ((q : ℝ)) ^ N = ((p : ℝ)) ^ M := by
    have hexp := congrArg Real.exp hlq
    rwa [Real.exp_log hqN, Real.exp_log hpM] at hexp
  have hnat : q ^ N = p ^ M := by exact_mod_cast heq
  have hpdvd : p ∣ q ^ N := hnat ▸ dvd_pow_self p hM.ne'
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpdvd))

/-- A positive integer cross-relation between two prime clock periods is impossible:
`a·(2π/log p) = b·(2π/log q)` with `a, b > 0` forces `a·log q = b·log p`, hence
`q^a = p^b` — excluded for distinct primes. -/
private lemma cross_pos_contra {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : (a : ℝ) * (2 * Real.pi / Real.log p) = (b : ℝ) * (2 * Real.pi / Real.log q)) :
    False := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  lift a to ℕ using ha.le with N
  lift b to ℕ using hb.le with M
  have hMpos : 0 < M := by exact_mod_cast hb
  have hcancel : (N : ℝ) * Real.log q = (M : ℝ) * Real.log p := by
    have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
    have hkey : ((N : ℝ) * Real.log q) * (2 * Real.pi)
        = ((M : ℝ) * Real.log p) * (2 * Real.pi) := by
      field_simp at h
      push_cast at h ⊢
      nlinarith [h]
    exact mul_right_cancel₀ h2π.ne' hkey
  exact prime_pow_log_contra hp hq hpq hMpos hcancel

/-- **One carrier, at most one prime clock.**  The divisor of a nonzero analytic function with
at least one zero cannot be invariant under the vertical clocks of two distinct primes: the
stabilizer is cyclic, so two member periods are commensurable, forcing `q^N = p^M` — impossible.
The dense rate spectrum of the primes can never act on a single divisor through more than one of
its clocks. -/
theorem vStab_one_prime_clock {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ)
    (hne : ∃ s, F s ≠ 0) (hz : ∃ s, F s = 0) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hps : (2 * Real.pi / Real.log p) ∈ vStab {s | F s = 0}) :
    (2 * Real.pi / Real.log q) ∉ vStab {s | F s = 0} := by
  intro hqs
  obtain ⟨c, hc⟩ := vStab_cyclic_of_analytic hF hne hz
  rw [hc] at hps hqs
  obtain ⟨m, hm⟩ := AddSubgroup.mem_closure_singleton.mp hps
  obtain ⟨n, hn⟩ := AddSubgroup.mem_closure_singleton.mp hqs
  rw [zsmul_eq_mul] at hm hn
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hTp : 0 < 2 * Real.pi / Real.log p := by
    exact div_pos (by positivity) (Real.log_pos hp1)
  have hTq : 0 < 2 * Real.pi / Real.log q := by
    exact div_pos (by positivity) (Real.log_pos hq1)
  have hcross : (n : ℝ) * (2 * Real.pi / Real.log p)
      = (m : ℝ) * (2 * Real.pi / Real.log q) := by
    rw [← hm, ← hn]; ring
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Int.cast_zero, zero_mul] at hn
    linarith
  rcases lt_or_gt_of_ne hn0 with hneg | hpos
  · have hmneg : (m : ℝ) < 0 := by
      have h1 : (n : ℝ) < 0 := by exact_mod_cast hneg
      nlinarith
    have hmneg' : m < 0 := by exact_mod_cast hmneg
    refine cross_pos_contra hp hq hpq (a := -n) (b := -m)
      (by omega) (by omega) ?_
    push_cast
    nlinarith [hcross]
  · have hmpos : (0 : ℝ) < m := by
      have h1 : (0 : ℝ) < n := by exact_mod_cast hpos
      nlinarith
    have hmpos' : 0 < m := by exact_mod_cast hmpos
    exact cross_pos_contra hp hq hpq hpos hmpos' hcross

end RHTower
