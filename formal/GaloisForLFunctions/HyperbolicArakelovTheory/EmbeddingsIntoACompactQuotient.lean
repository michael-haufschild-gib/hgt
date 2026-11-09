import GaloisForLFunctions.HyperbolicArakelovTheory.TheImagesOfTheDegreeGeodesic
import GaloisForLFunctions.SurfaceOfSpecZ.TheAtomicSurfaceHasGenusNLogN

/-!
# Embeddings of the degrees into a compact quotient

B118′(1) asks whether some lattice `Γ ⊂ SL₂(ℂ)` and some embedding `n ↦ w_n` of the degrees into
`Γ\ℍ³` reproduce the Frobenius intersection `2πG_{1/2}(|log(n/m)|) + Λ(n/m)(n/m)^{−1/2}` (normalized by
`√(mn)`) through an automorphic Green function. For a lattice the Poincaré series of `G_{1/2}`
diverges (`δ(Γ) = 2`), so such a kernel is a continued resolvent; whatever it is, it keeps the
Newtonian singularity of the free Green function on the diagonal.

**Theorem** (`not_eq_frobenius_of_mapClusterPt`, `not_eq_frobenius_of_compact`). Let `K` be a kernel
on a metric space that is unbounded above as two distinct points merge (`IsNewtonian`). No injective
embedding of the degrees with a cluster point reproduces the Frobenius intersection with any
normalization `κ` of its finite part. In particular no embedding into a compact quotient does.

**Mechanism.** Infinitely many degrees lie near the cluster point; among them pick `m` and `n ≥ 2m`.
Their images are close, so `K` is large, while on pairs of ratio `≥ 2` the target is bounded by
`2πG_{1/2}(log 2) + 2|κ|` (`frobeniusTarget_le`): the archimedean part decreases with the ratio and
`0 ≤ Λ(t)t^{−1/2} ≤ 2`.

In a lattice with cusps the same argument excludes every embedding with a bounded subsequence; the
embeddings that escape into the cusps are left, and there the growth of the cusp zero mode is the
expected obstruction (computed in `SurfaceOfSpecZ` for the vertical embedding).
-/

open Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ ArithmeticEffectivityTheory

/-- A kernel with a Newtonian singularity: it exceeds every bound on distinct close points. -/
def IsNewtonian {Y : Type*} [PseudoMetricSpace Y] (K : Y → Y → ℝ) : Prop :=
  ∀ B : ℝ, ∃ δ > 0, ∀ x y : Y, x ≠ y → dist x y < δ → B ≤ K x y

/-- On pairs of ratio `≥ 2` the normalized Frobenius intersection is bounded. -/
theorem frobeniusTarget_le {m n : ℕ} (hm : 0 < m) (h2 : 2 * m ≤ n) (κ : ℝ) :
    archProfile |Real.log n - Real.log m| + κ * weilPrimeKernel m n ≤
      archProfile (Real.log 2) + 2 * |κ| := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (2 : ℝ) * m ≤ n := by exact_mod_cast h2
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log 2 ≤ Real.log n - Real.log m := by
    rw [← Real.log_div hn0.ne' hm'.ne']
    exact Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hm']; linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : archProfile |Real.log n - Real.log m| ≤ archProfile (Real.log 2) := by
    rw [abs_of_nonneg (by linarith)]
    exact strictAntiOn_archProfile.antitoneOn (mem_Ioi.2 hl2) (mem_Ioi.2 (by linarith)) hlog
  have h2 : κ * weilPrimeKernel m n ≤ 2 * |κ| := by
    have h0 := weilPrimeKernel_nonneg m n
    have hle := weilPrimeKernel_le_two m n
    calc κ * weilPrimeKernel m n ≤ |κ| * weilPrimeKernel m n :=
          mul_le_mul_of_nonneg_right (le_abs_self κ) h0
      _ ≤ |κ| * 2 := mul_le_mul_of_nonneg_left hle (abs_nonneg κ)
      _ = 2 * |κ| := by ring
  linarith

/-- **No clustering embedding carries the Frobenius intersection.** -/
theorem not_eq_frobenius_of_mapClusterPt {Y : Type*} [PseudoMetricSpace Y] {K : Y → Y → ℝ}
    (hK : IsNewtonian K) {w : ℕ → Y} (hw : Function.Injective w) {y : Y}
    (hy : MapClusterPt y atTop w) (κ : ℝ) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      K (w m) (w n) = archProfile |Real.log n - Real.log m| + κ * weilPrimeKernel m n := by
  intro h
  obtain ⟨δ, hδ, hK'⟩ := hK (archProfile (Real.log 2) + 2 * |κ| + 1)
  have hfreq : ∃ᶠ n in atTop, w n ∈ Metric.ball y (δ / 2) :=
    (mapClusterPt_iff_frequently.mp hy) _ (Metric.ball_mem_nhds y (by linarith))
  obtain ⟨m, hmb, hm1⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
  obtain ⟨n, hnb, hn⟩ := (hfreq.and_eventually (eventually_ge_atTop (2 * m))).exists
  have hmn : m ≠ n := by omega
  have hd : dist (w m) (w n) < δ := by
    have h1 := Metric.mem_ball.mp hmb
    have h2 := Metric.mem_ball.mp hnb
    calc dist (w m) (w n) ≤ dist (w m) y + dist y (w n) := dist_triangle _ _ _
      _ = dist (w m) y + dist (w n) y := by rw [dist_comm y]
      _ < δ / 2 + δ / 2 := add_lt_add h1 h2
      _ = δ := by ring
  have hbig := hK' (w m) (w n) (hw.ne hmn) hd
  rw [h m n (by omega) (by omega) hmn] at hbig
  have := frobeniusTarget_le (by omega : 0 < m) hn κ
  linarith

/-- **No embedding into a compact quotient carries the Frobenius intersection.** -/
theorem not_eq_frobenius_of_compact {Y : Type*} [PseudoMetricSpace Y] [CompactSpace Y]
    {K : Y → Y → ℝ} (hK : IsNewtonian K) {w : ℕ → Y} (hw : Function.Injective w) (κ : ℝ) :
    ¬ ∀ m n : ℕ, 0 < m → 0 < n → m ≠ n →
      K (w m) (w n) = archProfile |Real.log n - Real.log m| + κ * weilPrimeKernel m n := by
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_mapClusterPt (f := atTop) (u := w)
    (tendsto_principal.mpr (Eventually.of_forall fun _ => mem_univ _))
  exact not_eq_frobenius_of_mapClusterPt hK hw hy κ

end GaloisForLFunctions.HyperbolicArakelovTheory
