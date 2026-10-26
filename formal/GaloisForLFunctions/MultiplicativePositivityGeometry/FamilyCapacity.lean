import GaloisForLFunctions.MultiplicativePositivityGeometry.AbelianZeroMass

/-!
# The capacity law for families is exact

For a family over a finite abelian group `G`, a pole-isolated configuration on `G × ℝ` is a pole of
order `k` at the origin and nonnegative zero masses `m(p)` at finitely many other points, with
`m(−p) = m(p)`. The zero-mass law on abelian groups (`family_capacity`) gives `Σ_{p ≠ 0} m(p) ≤ k`.

**Exactness** (`capFamily_isJointBoundaryDivisor`). Conversely every such configuration with
`Σ_p m(p) ≤ k` is a joint boundary divisor. The weights
`Λ(n) n^{−1−x} (k − Σ_{p ∈ S} m(p) Re(ψ(−p₁) n^{−ip₂}))/|G|` on the frequencies `(ψ, log n)` are
nonnegative because `Σ m(p) ≤ k`. By orthogonality of the characters of `G` their joint trace is
`k [g = 0] tr_ζ(u) − Σ_p (m(p)/2)([g = p₁] tr_ζ(u − p₂) + [g = −p₁] tr_ζ(u + p₂))`, which tends to
`k δ₀ − m`.

**Classification** (`family_isolated_iff`). An even real configuration on `G × ℝ` with finite
support, a pole of order `k` at the origin and no other pole is a joint boundary divisor iff its
total off-origin mass is at most `k`. Self-conjugate points (`2p = 0`) carry their mass once, all
others twice (with their conjugate): the capacity of a family is counted in self-conjugate units.
-/

open Finset Filter Topology Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

universe u

variable {G : Type u} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Orthogonality for joint modes: `Σ_ψ Re(ψ(g) e^{iλv}) = |G| [g = 0] cos(λv)`. -/
theorem sum_jointMode (lam : ℝ) (q : G × ℝ) :
    ∑ ψ : AddChar G ℂ, jointMode ψ lam q =
      Fintype.card G * (if q.1 = 0 then 1 else 0) * Real.cos (lam * q.2) := by
  simp only [jointMode, jointPhase]
  rw [← Complex.re_sum, ← Finset.sum_mul, AddChar.sum_apply_eq_ite]
  split_ifs
  · simp
    rw [← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · simp

/-- Products of two joint modes, summed over the characters. -/
theorem sum_jointMode_mul (lam : ℝ) (p q : G × ℝ) :
    ∑ ψ : AddChar G ℂ, jointMode ψ lam (-p) * jointMode ψ lam q =
      Fintype.card G / 2 * ((if q.1 = p.1 then 1 else 0) * Real.cos (lam * (q.2 - p.2)) +
        (if q.1 = -p.1 then 1 else 0) * Real.cos (lam * (q.2 + p.2))) := by
  have hprod : ∀ ψ : AddChar G ℂ, jointMode ψ lam (-p) * jointMode ψ lam q =
      (jointMode ψ lam (q - p) + jointMode ψ lam (-(p + q))) / 2 := by
    intro ψ
    simp only [jointMode]
    have e1 : jointPhase ψ lam (q - p) = jointPhase ψ lam q * jointPhase ψ lam (-p) := by
      rw [sub_eq_add_neg]
      unfold jointPhase
      rw [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul,
        show (((lam * (q.2 + (-p).2) : ℝ) : ℂ) * I) =
          ((lam * q.2 : ℝ) : ℂ) * I + ((lam * (-p).2 : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_add]
      ring
    have e2 : jointPhase ψ lam (-(p + q)) =
        jointPhase ψ lam (-p) * (starRingEnd ℂ) (jointPhase ψ lam q) := by
      have := jointPhase_sub ψ lam (-p) q
      rw [show -p - q = -(p + q) by abel] at this
      exact this
    rw [e1, e2, Complex.mul_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [Finset.sum_congr rfl fun ψ _ => hprod ψ, ← Finset.sum_div, Finset.sum_add_distrib,
    sum_jointMode, sum_jointMode]
  have h1 : (q - p).1 = 0 ↔ q.1 = p.1 := by simp [sub_eq_zero]
  have h2 : (-(p + q)).1 = 0 ↔ q.1 = -p.1 := by
    simp only [Prod.fst_neg, Prod.fst_add, neg_eq_zero]
    constructor
    · intro h; rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact h
    · intro h; rw [h, add_neg_cancel]
  simp only [h1, h2, Prod.snd_sub, Prod.snd_neg, Prod.snd_add]
  rw [show lam * -(p.2 + q.2) = -(lam * (q.2 + p.2)) by ring, Real.cos_neg]
  ring

/-- The capacity weights on the frequencies `(log n, ψ)`. -/
noncomputable def capFamWeight (k : ℝ) (S : Finset (G × ℝ)) (m : G × ℝ → ℝ) (x : ℝ)
    (q : ℕ × AddChar G ℂ) : ℝ :=
  zetaBoundaryWeight x q.1 *
    ((k - ∑ p ∈ S, m p * jointMode q.2 (logFrequency q.1) (-p)) / Fintype.card G)

/-- The configuration `k δ₀ − Σ_{p ∈ S} (m(p)/2)(δ_p + δ_{−p})`. -/
noncomputable def capFamDivisor (k : ℝ) (S : Finset (G × ℝ)) (m : G × ℝ → ℝ) (q : G × ℝ) : ℝ :=
  k * (if q = 0 then 1 else 0) -
    ∑ p ∈ S, m p / 2 * ((if q = p then 1 else 0) + (if q = -p then 1 else 0))

omit [DecidableEq G] in
theorem capFamWeight_nonneg {k : ℝ} {S : Finset (G × ℝ)} {m : G × ℝ → ℝ}
    (hm : ∀ p ∈ S, 0 ≤ m p) (hk : ∑ p ∈ S, m p ≤ k) (x : ℝ) (q : ℕ × AddChar G ℂ) :
    0 ≤ capFamWeight k S m x q := by
  unfold capFamWeight
  refine mul_nonneg (zetaBoundaryWeight_nonneg x q.1) (div_nonneg ?_ (Nat.cast_nonneg _))
  have : ∑ p ∈ S, m p * jointMode q.2 (logFrequency q.1) (-p) ≤ ∑ p ∈ S, m p :=
    Finset.sum_le_sum fun p hp => mul_le_of_le_one_right (hm p hp)
      ((le_abs_self _).trans (abs_jointMode_le _ _ _))
  linarith

omit [DecidableEq G] in
theorem capFamWeight_le {k : ℝ} {S : Finset (G × ℝ)} {m : G × ℝ → ℝ} (hm : ∀ p ∈ S, 0 ≤ m p)
    (x : ℝ) (q : ℕ × AddChar G ℂ) :
    capFamWeight k S m x q ≤ (|k| + ∑ p ∈ S, m p) * zetaBoundaryWeight x q.1 := by
  unfold capFamWeight
  have hG : (1 : ℝ) ≤ Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h1 : (k - ∑ p ∈ S, m p * jointMode q.2 (logFrequency q.1) (-p)) / Fintype.card G ≤
      |k| + ∑ p ∈ S, m p := by
    rw [div_le_iff₀ (by linarith)]
    have : -(∑ p ∈ S, m p) ≤ ∑ p ∈ S, m p * jointMode q.2 (logFrequency q.1) (-p) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun p hp => by
        have := abs_jointMode_le q.2 (logFrequency q.1) (-p)
        nlinarith [hm p hp, neg_abs_le (jointMode q.2 (logFrequency q.1) (-p))]
    have hS : 0 ≤ ∑ p ∈ S, m p := Finset.sum_nonneg hm
    have h2 : (|k| + ∑ p ∈ S, m p) * 1 ≤ (|k| + ∑ p ∈ S, m p) * Fintype.card G :=
      mul_le_mul_of_nonneg_left hG (add_nonneg (abs_nonneg k) hS)
    linarith [le_abs_self k]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (zetaBoundaryWeight_nonneg x q.1)

omit [DecidableEq G] in
theorem summable_capFamWeight {k : ℝ} {S : Finset (G × ℝ)} {m : G × ℝ → ℝ}
    (hm : ∀ p ∈ S, 0 ≤ m p) (hk : ∑ p ∈ S, m p ≤ k) {x : ℝ} (hx : 0 < x) :
    Summable (capFamWeight k S m x) := by
  refine Summable.of_nonneg_of_le (capFamWeight_nonneg hm hk x) (capFamWeight_le hm x) ?_
  refine (summable_prod_of_nonneg fun q => by
    have := zetaBoundaryWeight_nonneg x q.1
    have : 0 ≤ ∑ p ∈ S, m p := Finset.sum_nonneg hm
    positivity).mpr ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ((summable_zetaBoundaryWeight hx).mul_left _).mul_left _

/-- The capacity joint trace through the trace of `ζ`. -/
theorem jointTrace_capFam {k : ℝ} {S : Finset (G × ℝ)} {m : G × ℝ → ℝ} (hm : ∀ p ∈ S, 0 ≤ m p)
    (hk : ∑ p ∈ S, m p ≤ k) {x : ℝ} (hx : 0 < x) (q : G × ℝ) :
    jointTrace (capFamWeight k S m x) Prod.snd (fun r => logFrequency r.1) q =
      k * (if q.1 = 0 then 1 else 0) * cosineTrace (zetaBoundaryWeight x) logFrequency q.2 -
        ∑ p ∈ S, m p / 2 *
          ((if q.1 = p.1 then 1 else 0) *
              cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 - p.2) +
            (if q.1 = -p.1 then 1 else 0) *
              cosineTrace (zetaBoundaryWeight x) logFrequency (q.2 + p.2)) := by
  have hs := summable_jointTrace_terms (capFamWeight_nonneg hm hk x)
    (summable_capFamWeight hm hk hx) Prod.snd (fun r => logFrequency r.1) q
  have hz := zetaBoundaryWeight_nonneg x
  have hzs := summable_zetaBoundaryWeight hx
  have hC : ∀ v, HasSum (fun n => zetaBoundaryWeight x n * Real.cos (logFrequency n * v))
      (cosineTrace (zetaBoundaryWeight x) logFrequency v) := fun v =>
    (summable_cosineTrace_terms hz hzs logFrequency v).hasSum
  have hall := ((hC q.2).mul_left (k * (if q.1 = 0 then 1 else 0))).sub
    (hasSum_sum (s := S) fun p _ => (((hC (q.2 - p.2)).mul_left (if q.1 = p.1 then 1 else 0)).add
      ((hC (q.2 + p.2)).mul_left (if q.1 = -p.1 then 1 else 0))).mul_left (m p / 2))
  unfold jointTrace
  rw [hs.tsum_prod, ← hall.tsum_eq]
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  dsimp only
  set L := logFrequency n
  set z := zetaBoundaryWeight x n
  have step : ∀ ψ : AddChar G ℂ, capFamWeight k S m x (n, ψ) * jointMode ψ L q =
      z / Fintype.card G * (k * jointMode ψ L q -
        ∑ p ∈ S, m p * (jointMode ψ L (-p) * jointMode ψ L q)) := by
    intro ψ
    simp only [capFamWeight]
    have hs : (∑ p ∈ S, m p * jointMode ψ L (-p)) * jointMode ψ L q =
        ∑ p ∈ S, m p * (jointMode ψ L (-p) * jointMode ψ L q) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun p _ => by ring
    rw [← hs]
    simp only [L, z]
    ring
  simp only [step]
  set X : G × ℝ → ℝ := fun p => (if q.1 = p.1 then 1 else 0) * Real.cos (L * (q.2 - p.2)) +
    (if q.1 = -p.1 then 1 else 0) * Real.cos (L * (q.2 + p.2))
  have hL : ∑ ψ : AddChar G ℂ, z / Fintype.card G * (k * jointMode ψ L q -
      ∑ p ∈ S, m p * (jointMode ψ L (-p) * jointMode ψ L q)) =
      z / Fintype.card G * (k * (Fintype.card G * (if q.1 = 0 then 1 else 0) * Real.cos (L * q.2)) -
        Fintype.card G * ∑ p ∈ S, m p / 2 * X p) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_comm, sum_jointMode]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.mul_sum, sum_jointMode_mul]
    simp only [X]
    ring
  have hR : k * (if q.1 = 0 then 1 else 0) * (z * Real.cos (L * q.2)) -
      ∑ p ∈ S, m p / 2 * ((if q.1 = p.1 then 1 else 0) * (z * Real.cos (L * (q.2 - p.2))) +
        (if q.1 = -p.1 then 1 else 0) * (z * Real.cos (L * (q.2 + p.2)))) =
      k * (if q.1 = 0 then 1 else 0) * (z * Real.cos (L * q.2)) - z * ∑ p ∈ S, m p / 2 * X p := by
    rw [Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by simp only [X]; ring
  rw [hL, hR]
  field_simp

/-- **Exactness of the family capacity law.** If `m ≥ 0` on `S` and `Σ_{p ∈ S} m(p) ≤ k`,
the capacity weights are a joint boundary datum with divisor
`k δ₀ − Σ_{p ∈ S} (m(p)/2)(δ_p + δ_{−p})`. -/
theorem capFamily_isJointBoundaryDivisor {k : ℝ} {S : Finset (G × ℝ)} {m : G × ℝ → ℝ}
    (hm : ∀ p ∈ S, 0 ≤ m p) (hk : ∑ p ∈ S, m p ≤ k) :
    IsJointBoundaryDivisor Prod.snd (fun r : ℕ × AddChar G ℂ => logFrequency r.1)
      (capFamWeight k S m) (capFamDivisor k S m) where
  nonneg x _ q := capFamWeight_nonneg hm hk x q
  summable x hx := summable_capFamWeight hm hk hx
  tendsto q := by
    have hT : ∀ v, Tendsto (fun x => x * cosineTrace (zetaBoundaryWeight x) logFrequency v)
        (𝓝[>] 0) (𝓝 (if v = 0 then 1 else 0)) := fun v => by
      simpa only [zetaBoundaryDivisor_eq] using zeta_isBoundaryDivisor.tendsto v
    have hlim := ((hT q.2).const_mul (k * (if q.1 = 0 then 1 else 0))).sub
      (tendsto_finsetSum S fun p _ => (((hT (q.2 - p.2)).const_mul (if q.1 = p.1 then 1 else 0)).add
        ((hT (q.2 + p.2)).const_mul (if q.1 = -p.1 then 1 else 0))).const_mul (m p / 2))
    have heq : k * (if q.1 = 0 then 1 else 0) * (if q.2 = 0 then 1 else 0) -
        ∑ p ∈ S, m p / 2 * ((if q.1 = p.1 then 1 else 0) * (if q.2 - p.2 = 0 then 1 else 0) +
          (if q.1 = -p.1 then 1 else 0) * (if q.2 + p.2 = 0 then 1 else 0)) =
        capFamDivisor k S m q := by
      unfold capFamDivisor
      congr 1
      · obtain ⟨g, u⟩ := q
        by_cases hg : g = 0 <;> by_cases hu : u = 0 <;> simp [hg, hu, Prod.ext_iff]
      · refine Finset.sum_congr rfl fun p _ => ?_
        obtain ⟨g, u⟩ := q
        obtain ⟨g', u'⟩ := p
        congr 1
        congr 1
        · by_cases h1 : g = g' <;> by_cases h2 : u - u' = 0 <;>
            simp [h1, h2, Prod.ext_iff] <;> simp_all [sub_eq_zero]
        · by_cases h1 : g = -g' <;> by_cases h2 : u + u' = 0 <;>
            simp [h1, h2, Prod.ext_iff] <;> simp_all [add_eq_zero_iff_eq_neg]
    rw [heq] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [jointTrace_capFam hm hk (Set.mem_Ioi.mp hx), mul_sub, Finset.mul_sum]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun p _ => by ring

omit [Fintype G] in
/-- The capacity divisor of a symmetric even configuration is the configuration itself. -/
theorem capFamDivisor_eq {k : ℝ} {𝒟 : G × ℝ → ℝ} {S : Finset (G × ℝ)} (hS0 : (0 : G × ℝ) ∉ S)
    (hsupp : ∀ p, p ≠ 0 → p ∉ S → 𝒟 p = 0) (hSym : ∀ p ∈ S, -p ∈ S)
    (heven : ∀ p, 𝒟 (-p) = 𝒟 p) (h0 : 𝒟 0 = k) :
    capFamDivisor k S (fun p => -𝒟 p) = 𝒟 := by
  funext q
  unfold capFamDivisor
  have hsplit : ∑ p ∈ S, -𝒟 p / 2 * ((if q = p then (1 : ℝ) else 0) + (if q = -p then 1 else 0)) =
      (if q ∈ S then -𝒟 q / 2 else 0) + (if -q ∈ S then -𝒟 (-q) / 2 else 0) := by
    rw [← Finset.sum_ite_eq S q (fun p => -𝒟 p / 2), ← Finset.sum_ite_eq' S (-q) (fun p => -𝒟 p / 2),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e : (q = -p) ↔ (p = -q) := by constructor <;> intro h <;> rw [h, neg_neg]
    simp only [e]
    split_ifs <;> ring
  rw [hsplit]
  have hmem : q ∈ S ↔ -q ∈ S := ⟨hSym q, fun h => by simpa using hSym _ h⟩
  by_cases hq : q = 0
  · subst hq
    simp [hS0, h0]
  · rw [if_neg hq, heven]
    by_cases hqS : q ∈ S
    · rw [if_pos hqS, if_pos (hmem.mp hqS)]; ring
    · rw [if_neg hqS, if_neg (fun h => hqS (hmem.mpr h)), hsupp q hq hqS]; ring

/-- **The capacity law for families is exact.** For a symmetric finite support `S ∌ 0`, an even
configuration with pole order `k`, no other pole and support in `S ∪ {0}` is a joint boundary divisor
iff its total off-origin mass is at most `k`. -/
theorem family_isolated_iff {k : ℝ} {𝒟 : G × ℝ → ℝ} {S : Finset (G × ℝ)} (hS0 : (0 : G × ℝ) ∉ S)
    (hsupp : ∀ p, p ≠ 0 → p ∉ S → 𝒟 p = 0) (hSym : ∀ p ∈ S, -p ∈ S)
    (heven : ∀ p, 𝒟 (-p) = 𝒟 p) (h0 : 𝒟 0 = k) (hnp : ∀ p, p ≠ 0 → 𝒟 p ≤ 0) :
    (∃ (ι : Type u) (ψ : ι → AddChar G ℂ) (lam : ι → ℝ) (w : ℝ → ι → ℝ),
        IsJointBoundaryDivisor ψ lam w 𝒟) ↔ ∑ p ∈ S, -𝒟 p ≤ k := by
  constructor
  · rintro ⟨ι, ψ, lam, w, hw⟩
    rw [← h0]
    exact total_offOrigin_mass_le hw.isEvenPosDef hnp hS0
  · intro hk
    have hm : ∀ p ∈ S, 0 ≤ -𝒟 p := fun p hp => by
      have := hnp p (fun h => hS0 (h ▸ hp)); linarith
    have h := capFamily_isJointBoundaryDivisor (G := G) hm hk
    rw [capFamDivisor_eq hS0 hsupp hSym heven h0] at h
    exact ⟨_, _, _, _, h⟩

end GaloisForLFunctions.MultiplicativePositivityGeometry
