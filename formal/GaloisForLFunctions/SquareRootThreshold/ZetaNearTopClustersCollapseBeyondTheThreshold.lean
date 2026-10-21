import GaloisForLFunctions.SquareRootThreshold.ZetaTwinsAreExponentiallyTightUnlessTripled

/-!
# Near-top clusters collapse beyond the threshold

The elimination of `ZetaTwinsAreExponentiallyTightUnlessTripled` iterates. On sequences
`A(m) = Σ_z D(z) K_m(x(z))` the operator
`(E_y A)(m) = (y + β²_{j+1}) A(m + 1) − c_{j+1} A(m)` multiplies the term of `z` by `y − x(z)²` and raises
the order by one, so it kills the exponents with `x(z)² = y`. Composing over a cluster gives the
sequence (`elimSeq`)
`Φ(ys, m) = Σ_z D(z) Π_{y ∈ ys}(y − x(z)²) K_{m+|ys|}(x(z))`, with the step identity `elimSeq_cons`.

* **Noise is preserved** (`norm_elimSeq_le`). If the cluster sums have the noise
  `(2m)!(π/V)^{2m} (4/3)^m Ξ/r^{2m+1}` at every order and the eliminated points satisfy `|y| ≤ r²`,
  `Vr ≥ 4π(m + |ys|)`, then each elimination costs only the factor `8/3`.
* **What survives** (`elimSeq_eq_record_add`). Eliminating the companions leaves the record with the
  factor `Π (x(z)² − x(z*)²)` and the members that were not eliminated.
* **Cluster collapse for `ζ`** (`zeta_cluster_collapse`, `zeta_cluster_collapse_explicit`). Let `S`
  be the exponents within `r` of `s = z* − κ/V`, all others at distance `≥ r`. The loud companions
  (`Re z ≥ Re s`) are eliminated through the orders `k, …, k + p`; since
  `x(z)² − x(z*)² = (z − z*)(x(z) + κ/V)` with `|x(z) + κ/V| ≥ κ/V`, positivity on `[0, V]` gives
  `|D(z*)| Π|z − z*| (κ/V)^p |K_{k+p}(κ/V)| ≤ (2(k+p))!(π/V)^{2(k+p)} (8/3)^p (4/3)^k Ξ/r^{2k+1}
    + (Σ_{quiet}|D|)(2r²)^p V`,
  and with no quiet members
  `|D(z*)|(e^κ − 1) κ^p V^{2k+p+1} r^{2k+1} Π_{z ∈ S_L}|z − z*| ≤ κ (8/3)^p (4/3)^k (κ² + 4π²(k+p)²)^{k+p} Ξ`.

With `B = κ + 2π(k + p)` and `Vr ≥ λB` this reads
`(Π|z − z*|)^{1/p} ≤ (8B²/(3κV)) (Ξ'(4/3)^k κ/(λ^{2k+1}B))^{1/p}`: the geometric mean of the distances of
the `p` loud companions to the record decays like `e^{−ck/p}` with the order `k ≍ Vr`. A cluster of
`p` members can hide a record only if its geometric-mean radius is `O(r e^{−cVr/p})`. Since `p` is at
most the local count `O(log γ)`, the collapse sets in once `Vr ≫ log γ`, beyond the square-root
threshold `V ≍ log T`: there, positivity forces the near-top zeros around a record into a cluster
of exponentially small diameter, an approximate multiple zero.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Iterated elimination across Fejér orders -/

/-- The cluster sequence after eliminating the points `ys`:
`Φ(ys, m) = Σ_{z ∈ S} D(z) Π_{y ∈ ys} (y − x(z)²) K_{m + |ys|}(x(z))`. -/
def elimSeq (V : ℝ) (S : Finset ℂ) (D x : ℂ → ℂ) (ys : List ℂ) (m : ℕ) : ℂ :=
  ∑ z ∈ S, D z * (ys.map fun y => y - x z ^ 2).prod * fejerPowWin (m + ys.length) V (x z)

/-- **One elimination step.** `Φ(y :: ys, m) = (y + β²) Φ(ys, m + 1) − c Φ(ys, m)` with
`β = (2j+2)π/V`, `c = (2j+2)(2j+1)(π/V)²`, `j = m + |ys|`. -/
theorem elimSeq_cons {V : ℝ} (hV : 0 < V) (S : Finset ℂ) (D x : ℂ → ℂ) (y : ℂ) (ys : List ℂ)
    (m : ℕ) :
    elimSeq V S D x (y :: ys) m =
      (y + (((2 * (m + ys.length : ℕ) + 2) * π / V : ℝ) : ℂ) ^ 2) * elimSeq V S D x ys (m + 1) -
        (((2 * (m + ys.length : ℕ) + 2) * (2 * (m + ys.length : ℕ) + 1) * (π / V) ^ 2 : ℝ) : ℂ) *
          elimSeq V S D x ys m := by
  unfold elimSeq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  have h := fejerPowWin_succ hV (m + ys.length) (x z)
  have e1 : m + (y :: ys).length = m + ys.length + 1 := by simp; ring
  have e2 : m + 1 + ys.length = m + ys.length + 1 := by ring
  rw [e1, e2, List.map_cons, List.prod_cons]
  push_cast at h ⊢
  linear_combination (-(D z * (ys.map fun y => y - x z ^ 2).prod)) * h

/-- **Elimination preserves the noise level.** If the cluster sequence satisfies
`|Φ([], m')| ≤ (2m')!(π/V)^{2m'} (4/3)^{m'} Ξ/r^{2m'+1}` for `m ≤ m' ≤ m + |ys|`, every eliminated
point has `|y| ≤ r²`, and `Vr ≥ 4π(m + |ys|)`, then
`|Φ(ys, m)| ≤ (2(m + |ys|))!(π/V)^{2(m+|ys|)} (8/3)^{|ys|} (4/3)^m Ξ/r^{2m+1}`. -/
theorem norm_elimSeq_le {V r Ξ : ℝ} (hV : 0 < V) (hr : 0 < r) (hΞ : 0 ≤ Ξ) (S : Finset ℂ)
    (D x : ℂ → ℂ) (ys : List ℂ) (m : ℕ) (hys : ∀ y ∈ ys, ‖y‖ ≤ r ^ 2)
    (hVr : 4 * π * (m + ys.length : ℕ) ≤ V * r)
    (hA : ∀ m' : ℕ, m ≤ m' → m' ≤ m + ys.length → ‖elimSeq V S D x [] m'‖ ≤
      (2 * m').factorial * (π / V) ^ (2 * m') * ((4 / 3) ^ m' * Ξ / r ^ (2 * m' + 1))) :
    ‖elimSeq V S D x ys m‖ ≤ (2 * (m + ys.length)).factorial * (π / V) ^ (2 * (m + ys.length)) *
      ((8 / 3) ^ ys.length * (4 / 3) ^ m * Ξ / r ^ (2 * m + 1)) := by
  induction ys generalizing m with
  | nil =>
    have := hA m le_rfl (by simp)
    simpa using this
  | cons y ys ih =>
    set p := ys.length with hp
    set j := m + p with hj
    have hlen : (y :: ys).length = p + 1 := by simp [hp]
    have hys' : ∀ y' ∈ ys, ‖y'‖ ≤ r ^ 2 := fun y' hy' => hys y' (List.mem_cons_of_mem _ hy')
    have hy : ‖y‖ ≤ r ^ 2 := hys y List.mem_cons_self
    rw [hlen] at hVr hA ⊢
    have ih1 := ih (m + 1) hys' (by push_cast at hVr ⊢; linarith) fun m' h1 h2 => hA m' (by omega)
      (by omega)
    have ih0 := ih m hys' (by push_cast at hVr ⊢; nlinarith [Real.pi_pos]) fun m' h1 h2 =>
      hA m' h1 (by omega)
    rw [elimSeq_cons hV]
    set β : ℝ := (2 * (m + p : ℕ) + 2) * π / V with hβ
    set c : ℝ := (2 * (m + p : ℕ) + 2) * (2 * (m + p : ℕ) + 1) * (π / V) ^ 2 with hc
    have hβ0 : 0 ≤ β := by rw [hβ]; positivity
    have hβr : 2 * β ≤ r := by
      rw [hβ, show 2 * ((2 * ((m + p : ℕ) : ℝ) + 2) * π / V) = 4 * π * ((m + p : ℕ) + 1) / V by
        ring, div_le_iff₀ hV]
      push_cast at hVr ⊢; linarith
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hyβ : ‖y + ((β : ℝ) : ℂ) ^ 2‖ ≤ 5 / 4 * r ^ 2 := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hβ0]
      nlinarith
    -- units: `c u_j = u_{j+1}`
    have hcu : c * ((2 * (m + p)).factorial * (π / V) ^ (2 * (m + p))) =
        (2 * (m + (p + 1))).factorial * (π / V) ^ (2 * (m + (p + 1))) := by
      rw [hc, show 2 * (m + (p + 1)) = (2 * (m + p) + 1) + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ, show (2 * (m + p) + 1) + 1 = 2 * (m + p) + 2 by ring, pow_add]
      push_cast; ring
    have e1 : m + 1 + p = m + (p + 1) := by ring
    rw [e1] at ih1
    set U := (2 * (m + (p + 1))).factorial * (π / V) ^ (2 * (m + (p + 1))) with hU
    set G := (8 / 3) ^ p * (4 / 3) ^ m * Ξ / r ^ (2 * m + 1) with hG
    have hG0 : 0 ≤ G := by rw [hG]; positivity
    have hU0 : 0 ≤ U := by rw [hU]; positivity
    have h1 : (8 / 3) ^ p * (4 / 3) ^ (m + 1) * Ξ / r ^ (2 * (m + 1) + 1) = 4 / 3 * G / r ^ 2 := by
      rw [hG, show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, pow_add, pow_succ]; field_simp; ring
    rw [h1] at ih1
    calc ‖(y + ((β : ℝ) : ℂ) ^ 2) * elimSeq V S D x ys (m + 1) - (c : ℂ) * elimSeq V S D x ys m‖
        ≤ ‖y + ((β : ℝ) : ℂ) ^ 2‖ * ‖elimSeq V S D x ys (m + 1)‖ + c * ‖elimSeq V S D x ys m‖ := by
          refine (norm_sub_le _ _).trans (le_of_eq ?_)
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0]
      _ ≤ 5 / 4 * r ^ 2 * (U * (4 / 3 * G / r ^ 2)) +
            c * ((2 * (m + p)).factorial * (π / V) ^ (2 * (m + p)) * G) :=
          add_le_add (mul_le_mul hyβ ih1 (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left ih0 hc0)
      _ = U * ((8 / 3) ^ (p + 1) * (4 / 3) ^ m * Ξ / r ^ (2 * m + 1)) := by
          have hr2 : r ^ 2 ≠ 0 := by positivity
          rw [show c * ((2 * (m + p)).factorial * (π / V) ^ (2 * (m + p)) * G) =
            (c * ((2 * (m + p)).factorial * (π / V) ^ (2 * (m + p)))) * G by ring, hcu]
          rw [hG, pow_succ]; field_simp; ring

/-- **What survives the elimination.** Eliminating the points `x(z)²`, `z ∈ S_L`, kills the terms of
`S_L` and leaves the record `z₁` with the factor `Π_{z ∈ S_L}(x(z)² − x(z₁)²)`, plus the
non-eliminated rest of `S`. -/
theorem elimSeq_eq_record_add (V : ℝ) (S SL : Finset ℂ) (D x : ℂ → ℂ) {z₁ : ℂ} (hz₁ : z₁ ∈ S)
    (hz₁L : z₁ ∉ SL) (m : ℕ) :
    elimSeq V S D x (SL.toList.map fun z => x z ^ 2) m =
      D z₁ * (∏ z' ∈ SL, (x z' ^ 2 - x z₁ ^ 2)) * fejerPowWin (m + SL.card) V (x z₁) +
        ∑ z ∈ (S.filter fun z => z ∉ SL).erase z₁,
          D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (m + SL.card) V (x z) := by
  classical
  unfold elimSeq
  rw [List.length_map, Finset.length_toList]
  have hprod : ∀ z, ((SL.toList.map fun z => x z ^ 2).map fun y => y - x z ^ 2).prod =
      ∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2) := fun z => by
    rw [List.map_map]; exact Finset.prod_map_toList _ _
  simp_rw [hprod]
  rw [← Finset.sum_filter_add_sum_filter_not S (fun z => z ∈ SL)]
  have h0 : ∑ z ∈ S.filter (fun z => z ∈ SL),
      D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (m + SL.card) V (x z) = 0 :=
    Finset.sum_eq_zero fun z hz => by
      have : ∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2) = 0 :=
        Finset.prod_eq_zero (f := fun z' => x z' ^ 2 - x z ^ 2) (Finset.mem_filter.mp hz).2
          (sub_self _)
      rw [this, mul_zero, zero_mul]
  rw [h0, zero_add]
  have hmem : z₁ ∈ S.filter fun z => z ∉ SL := Finset.mem_filter.mpr ⟨hz₁, hz₁L⟩
  rw [← Finset.add_sum_erase _ _ hmem]

/-! ### The cluster-collapse inequality for `ζ` -/

/-- **Cluster collapse for `ζ`.** Let the difference tests of a `C²` bump be Weil nonnegative on
`[0, V]`, `z*` the Legendre record at lag `V`, `κ > 0`, `σ = Re z* − κ/V`, `s = σ + i Im z*`,
`0 < r ≤ min(1, σ)`, `k ≥ 1`, and let `S ∋ z*` be the exponents within `r` of `s` (all others keep
distance `r`). Let `S_L` be the loud companions (`z ≠ z*`, `Re z ≥ σ`), `p = |S_L|`, and
`V ≥ π(k + p)`, `Vr ≥ 4π(k + p)`. Eliminating `S_L` through the orders `k, …, k + p` gives
`|D(z*)| Π_{z ∈ S_L}|z − z*| (κ/V)^p |K_{k+p}(κ/V)| ≤ (2(k+p))!(π/V)^{2(k+p)} (8/3)^p (4/3)^k Ξ/r^{2k+1}
  + (Σ_{quiet} |D(z)|)(2r²)^p V`,
`Ξ = 4|M| + 4W + 3840 L |D(z*)| e^κ`, `L = log(180(|Im z*| + 6))`, the quiet members being those with
`Re z < σ`. -/
theorem zeta_cluster_collapse {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ}
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hr1 : r ≤ 1) (hrσ : r ≤ z₁.re - κ / V) {k : ℕ}
    (hk : 1 ≤ k) (S : Finset ℂ) (hz₁S : z₁ ∈ S)
    (hSr : ∀ z ∈ S, ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ ≤ r)
    (hiso : ∀ z, z ∉ S → evenCoeff zetaZeroConfig b z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖)
    (hV : π * (k + (S.filter fun z => z ≠ z₁ ∧ 0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re).card :
      ℕ) ≤ V)
    (hVr : 4 * π * (k + (S.filter fun z => z ≠ z₁ ∧
      0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re).card : ℕ) ≤ V * r) :
    ‖evenCoeff zetaZeroConfig b z₁‖ *
        (∏ z ∈ S.filter (fun z => z ≠ z₁ ∧ 0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re),
          ‖z - z₁‖) *
        (κ / V) ^ (S.filter fun z => z ≠ z₁ ∧
          0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re).card *
        ‖fejerPowWin (k + (S.filter fun z => z ≠ z₁ ∧
          0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re).card) V ((κ / V : ℝ) : ℂ)‖ ≤
      (2 * (k + (S.filter fun z => z ≠ z₁ ∧
          0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re).card)).factorial *
        (π / V) ^ (2 * (k + (S.filter fun z => z ≠ z₁ ∧
          0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re).card)) *
        ((8 / 3) ^ (S.filter fun z => z ≠ z₁ ∧
            0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re).card * (4 / 3) ^ k *
          (4 * |2 * (lagStructure zetaZeroConfig b 0).re| +
            4 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) +
            3840 * Real.log (180 * (|z₁.im| + 6)) * ‖evenCoeff zetaZeroConfig b z₁‖ *
              Real.exp κ) / r ^ (2 * k + 1)) +
      (∑ z ∈ S.filter (fun z => (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re < 0),
          ‖evenCoeff zetaZeroConfig b z‖) *
        (2 * r ^ 2) ^ (S.filter fun z => z ≠ z₁ ∧
          0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re).card * V := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  set SL := S.filter fun z => z ≠ z₁ ∧ 0 ≤ (z - s).re with hSL
  set p := SL.card with hp
  set M : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set L : ℝ := Real.log (180 * (|z₁.im| + 6)) with hL
  set Ξ : ℝ := 4 * |M| + 4 * W + 3840 * L * ‖D z₁‖ * Real.exp κ with hΞ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [abs_nonneg z₁.im])
  have hΞ0 : 0 ≤ Ξ := by rw [hΞ]; positivity
  have hσ : 0 < z₁.re - κ / V := lt_of_lt_of_le hr hrσ
  set x : ℂ → ℂ := fun z => z - s with hx
  -- the noise of the cluster at every order `k ≤ m' ≤ k + p`
  have hA : ∀ m' : ℕ, k ≤ m' → m' ≤ k + p → ‖elimSeq V S D x [] m'‖ ≤
      (2 * m').factorial * (π / V) ^ (2 * m') * ((4 / 3) ^ m' * Ξ / r ^ (2 * m' + 1)) := by
    intro m' h1 h2
    have hm1 : 1 ≤ m' := le_trans hk h1
    have hm'r : (m' : ℝ) ≤ (k + p : ℕ) := by exact_mod_cast h2
    have hcl := zeta_powCluster_le hb hbs (j := m') hm1 (by nlinarith [Real.pi_pos]) hm hz₁ hrec hκ
      hσ hr (by linarith) (by nlinarith [Real.pi_pos]) S hiso
    have hbr := clusterBracket_le (j := m') hm1 (M := M) (W := W) (D := ‖D z₁‖) (κ := κ) z₁.im hW0
      (norm_nonneg _) hr hr1 hrσ
    have e : elimSeq V S D x [] m' = ∑ z ∈ S, D z * fejerPowWin m' V (z - s) := by
      simp [elimSeq, hx]
    rw [e]
    refine hcl.trans ?_
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) hbr) (by positivity)
    rfl
  -- eliminate the loud companions
  set ys : List ℂ := SL.toList.map fun z => x z ^ 2 with hys
  have hlen : ys.length = p := by rw [hys, List.length_map, Finset.length_toList]
  have hysr : ∀ y ∈ ys, ‖y‖ ≤ r ^ 2 := by
    intro y hy
    rw [hys, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Finset.mem_toList, hSL, Finset.mem_filter] at hz
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hSr z hz.1) 2
  have hΦ := norm_elimSeq_le hV0 hr hΞ0 S D x ys k hysr (by rw [hlen]; exact hVr)
    (fun m' h1 h2 => hA m' h1 (by rw [hlen] at h2; exact h2))
  rw [hlen] at hΦ
  have hz₁L : z₁ ∉ SL := fun h => (Finset.mem_filter.mp h).2.1 rfl
  have hdecomp := elimSeq_eq_record_add V S SL D x hz₁S hz₁L k
  rw [← hys] at hdecomp
  -- the rest consists of quiet members
  set R := (S.filter fun z => z ∉ SL).erase z₁ with hR
  set Q := S.filter fun z => (z - s).re < 0 with hQ
  have hRQ : R ⊆ Q := by
    intro z hz
    rw [hR, Finset.mem_erase, Finset.mem_filter] at hz
    rw [hQ, Finset.mem_filter]
    refine ⟨hz.2.1, ?_⟩
    by_contra h; push Not at h
    exact hz.2.2 (Finset.mem_filter.mpr ⟨hz.2.1, hz.1, h⟩)
  have hrest : ‖∑ z ∈ R, D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z)‖ ≤
      (∑ z ∈ Q, ‖D z‖) * (2 * r ^ 2) ^ p * V := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ z ∈ R, ‖D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z)‖ ≤
        ‖D z‖ * ((2 * r ^ 2) ^ p * V) := fun z hz => by
      have hzQ := hRQ hz
      rw [hQ, Finset.mem_filter] at hzQ
      rw [norm_mul, norm_mul, norm_prod, mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul ?_ ?_ (norm_nonneg _) (by positivity))
        (norm_nonneg _)
      · rw [← Finset.prod_const]
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun z' hz' => ?_
        have h1 := hSr z' (Finset.mem_filter.mp hz').1
        have h2 := hSr z hzQ.1
        refine (norm_sub_le _ _).trans ?_
        rw [norm_pow, norm_pow]
        have := pow_le_pow_left₀ (norm_nonneg _) h1 2
        have := pow_le_pow_left₀ (norm_nonneg _) h2 2
        simp only [hx] at *
        linarith
      · have := norm_fejerPowWin_le_max hV0.le (k + p) (x z)
        refine this.trans (le_of_eq ?_)
        rw [max_eq_left (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hzQ.2.le hV0.le)),
          mul_one]
    calc ∑ z ∈ R, ‖D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z)‖
        ≤ ∑ z ∈ R, ‖D z‖ * ((2 * r ^ 2) ^ p * V) := Finset.sum_le_sum hterm
      _ ≤ ∑ z ∈ Q, ‖D z‖ * ((2 * r ^ 2) ^ p * V) :=
          Finset.sum_le_sum_of_subset_of_nonneg hRQ fun _ _ _ => by positivity
      _ = _ := by rw [← Finset.sum_mul]; ring
  -- the record term
  have hx₁ : x z₁ = ((κ / V : ℝ) : ℂ) := by
    simp only [hx]; apply Complex.ext <;> simp [hs]
  have hθ0 : 0 < κ / V := div_pos hκ hV0
  have hprod : (∏ z ∈ SL, ‖z - z₁‖) * (κ / V) ^ p ≤ ‖∏ z' ∈ SL, (x z' ^ 2 - x z₁ ^ 2)‖ := by
    rw [norm_prod, hp, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun z hz => ?_
    rw [Finset.mem_filter] at hz
    have e : x z ^ 2 - x z₁ ^ 2 = (z - z₁) * (x z + ((κ / V : ℝ) : ℂ)) := by
      rw [hx₁]; simp only [hx]
      have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
      linear_combination (z - s + ((κ / V : ℝ) : ℂ)) * this
    rw [e, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.add_re, Complex.ofReal_re]
    simp only [hx]
    linarith [hz.2.2]
  have hrecn : ‖D z₁ * (∏ z' ∈ SL, (x z' ^ 2 - x z₁ ^ 2)) * fejerPowWin (k + p) V (x z₁)‖ ≤
      ‖elimSeq V S D x ys k‖ +
        ‖∑ z ∈ R, D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z)‖ := by
    rw [hdecomp]
    have := norm_sub_le (D z₁ * (∏ z' ∈ SL, (x z' ^ 2 - x z₁ ^ 2)) * fejerPowWin (k + p) V (x z₁) +
      ∑ z ∈ R, D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z))
      (∑ z ∈ R, D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z))
    rw [add_sub_cancel_right] at this
    linarith
  rw [norm_mul, norm_mul, hx₁] at hrecn
  rw [hx₁] at hprod
  calc ‖D z₁‖ * (∏ z ∈ SL, ‖z - z₁‖) * (κ / V) ^ p * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖
      = ‖D z₁‖ * ((∏ z ∈ SL, ‖z - z₁‖) * (κ / V) ^ p) *
          ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by ring
    _ ≤ ‖D z₁‖ * ‖∏ z' ∈ SL, (x z' ^ 2 - ((κ / V : ℝ) : ℂ) ^ 2)‖ *
          ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
        gcongr
    _ ≤ _ := hrecn.trans (add_le_add hΦ hrest)

/-- **Explicit cluster collapse.** Under the hypotheses of `zeta_cluster_collapse`, if no member of
the cluster lies left of `s` (`Re z ≥ σ` on `S`), then with `p = |S_L|`,
`Q = (κ² + 4π²(k+p)²)^{k+p}`:
`|D(z*)| (e^κ − 1) κ^p V^{2k+p+1} r^{2k+1} Π_{z ∈ S_L}|z − z*| ≤ κ (8/3)^p (4/3)^k Q Ξ`. -/
theorem zeta_cluster_collapse_explicit {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ}
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hr1 : r ≤ 1) (hrσ : r ≤ z₁.re - κ / V) {k : ℕ}
    (hk : 1 ≤ k) (S : Finset ℂ) (hz₁S : z₁ ∈ S)
    (hSr : ∀ z ∈ S, ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ ≤ r)
    (hSright : ∀ z ∈ S, 0 ≤ (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)).re)
    (hiso : ∀ z, z ∉ S → evenCoeff zetaZeroConfig b z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖)
    (hV : π * (k + (S.erase z₁).card : ℕ) ≤ V)
    (hVr : 4 * π * (k + (S.erase z₁).card : ℕ) ≤ V * r) :
    ‖evenCoeff zetaZeroConfig b z₁‖ * (Real.exp κ - 1) * κ ^ (S.erase z₁).card *
        V ^ (2 * k + (S.erase z₁).card + 1) * r ^ (2 * k + 1) *
        (∏ z ∈ S.erase z₁, ‖z - z₁‖) ≤
      κ * (8 / 3) ^ (S.erase z₁).card * (4 / 3) ^ k *
        (κ ^ 2 + 4 * π ^ 2 * (k + (S.erase z₁).card : ℕ) ^ 2) ^ (k + (S.erase z₁).card) *
        (4 * |2 * (lagStructure zetaZeroConfig b 0).re| +
          4 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) +
          3840 * Real.log (180 * (|z₁.im| + 6)) * ‖evenCoeff zetaZeroConfig b z₁‖ *
            Real.exp κ) := by
  classical
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hSL : (S.filter fun z => z ≠ z₁ ∧ 0 ≤ (z - s).re) = S.erase z₁ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1, hSright z h2⟩
  have hQ : (S.filter fun z => (z - s).re < 0) = ∅ := by
    ext z
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
    exact hSright z
  have hcol := zeta_cluster_collapse hb hbs hm hz₁ hrec hκ hr hr1 hrσ hk S hz₁S hSr hiso
    (by rw [← hs, hSL]; exact hV) (by rw [← hs, hSL]; exact hVr)
  rw [← hs, hSL, hQ, Finset.sum_empty, zero_mul, zero_mul, add_zero] at hcol
  set p := (S.erase z₁).card with hp
  set Pz := ∏ z ∈ S.erase z₁, ‖z - z₁‖ with hPz
  set Ξ := 4 * |2 * (lagStructure zetaZeroConfig b 0).re| +
    4 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) +
    3840 * Real.log (180 * (|z₁.im| + 6)) * ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp κ with hΞ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hθ0 : 0 < κ / V := div_pos hκ hV0
  set Q := (κ ^ 2 + 4 * π ^ 2 * (k + p : ℕ) ^ 2) ^ (k + p) with hQ
  have hQ0 : 0 < Q := by positivity
  set u := (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) with hu
  have hu0 : 0 < u := by positivity
  -- the record kernel
  have hlow := norm_fejerPowWin_ofReal_ge hV0 (k + p) hθ0
  have hlow' : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
      ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) hlow
    have hVne : V ≠ 0 := hV0.ne'
    have hκne : κ ≠ 0 := hκ.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + p : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * (k + p : ℕ) ^ 2) / V ^ 2 := by field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu, hQ, div_pow, div_pow, ← pow_mul V 2 (k + p), pow_succ]
    field_simp
  have hD0 : 0 ≤ ‖evenCoeff zetaZeroConfig b z₁‖ := norm_nonneg _
  have hPz0 : 0 ≤ Pz := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have h1 : ‖evenCoeff zetaZeroConfig b z₁‖ * Pz * (κ / V) ^ p *
      (u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q)) ≤
      u * ((8 / 3) ^ p * (4 / 3) ^ k * Ξ / r ^ (2 * k + 1)) :=
    le_trans (mul_le_mul_of_nonneg_left hlow' (by positivity)) hcol
  have hr0 : 0 < r ^ (2 * k + 1) := by positivity
  have e2 : ‖evenCoeff zetaZeroConfig b z₁‖ * Pz * (κ / V) ^ p *
      (u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q)) =
      u * (‖evenCoeff zetaZeroConfig b z₁‖ * (Real.exp κ - 1) * κ ^ p * V ^ (2 * k + p + 1) * Pz /
        (κ * Q)) := by
    have hVne : V ≠ 0 := hV0.ne'
    have hκne : κ ≠ 0 := hκ.ne'
    rw [div_pow, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add]
    field_simp
  rw [e2] at h1
  have h2 := le_of_mul_le_mul_left h1 hu0
  rw [div_le_div_iff₀ (by positivity) hr0] at h2
  calc ‖evenCoeff zetaZeroConfig b z₁‖ * (Real.exp κ - 1) * κ ^ p * V ^ (2 * k + p + 1) *
        r ^ (2 * k + 1) * Pz
      = ‖evenCoeff zetaZeroConfig b z₁‖ * (Real.exp κ - 1) * κ ^ p * V ^ (2 * k + p + 1) * Pz *
          r ^ (2 * k + 1) := by ring
    _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * Ξ * (κ * Q) := h2
    _ = _ := by ring

end GaloisForLFunctions.SquareRootThreshold
