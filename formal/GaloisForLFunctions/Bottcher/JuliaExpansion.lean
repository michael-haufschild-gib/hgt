/-
# Böttcher tower — expansion on the disconnected filled Julia set (hyperbolicity foundation)

For disconnected `c` the escaping critical point `0` lies OFF `K_c`, so `K_c` is bounded away from `0`
and the iterated derivative grows multiplicatively along every orbit in `K_c`. This is the analytic
foundation of the Branner–Hubbard / Mañé hyperbolicity of the disconnected Julia set: the expansion
forces the inverse branches to contract, so the nested depth-`n` cylinders shrink to a Cantor set — the
carrier of the unbounded-order dyadic monodromy of `φ_{c₁}` that the disconnected case of `q62` needs
(`Q62RadicalReduction.q62_disconnected_of_radical_data`: the lone remaining input is, per depth `k`, a
`c₁`-cylinder loop with primitive `2^k` `φ_{c₁}`-monodromy lying in a `K_{c₂}`-free ball, so that
`φ_{c₂}` is deck-fixed — `JuliaSeparation.exists_ball_filledJulia_one_not_other`).
-/
import GaloisForLFunctions.Bottcher.BasinBranching
import Mathlib.Analysis.Complex.Schwarz

open Complex Set

namespace Bottcher

/-- **`K_c` is bounded away from the critical point for disconnected `c`.** Since `0 ∉ K_c`
(`disconnected_iff_zero_not_mem`) and `K_c` is compact, the modulus `‖·‖` attains a positive minimum
`δ > 0` on `K_c`: every point of the filled Julia set has `δ ≤ ‖z‖`. With forward-invariance this means
the whole forward orbit of any `z ∈ K_c` avoids a fixed neighborhood of the escaping critical point —
the dynamical source of expansion on `K_c`. -/
theorem exists_min_norm_filledJulia_pos {c : ℂ} (hc : Disconnected c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ filledJulia c, δ ≤ ‖z‖ := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  rcases (filledJulia c).eq_empty_or_nonempty with hemp | hne
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    rw [hemp] at hz
    simp only [Set.mem_empty_iff_false] at hz
  · obtain ⟨z₀, hz₀mem, hz₀min⟩ :=
      (isCompact_filledJulia c).exists_isMinOn hne continuous_norm.continuousOn
    have hz₀ne : z₀ ≠ 0 := fun h => h0 (h ▸ hz₀mem)
    exact ⟨‖z₀‖, norm_pos_iff.mpr hz₀ne, fun z hz => hz₀min hz⟩

/-- **Multiplicative expansion along the orbit on `K_c`.** For disconnected `c` with minimal modulus
`δ > 0` on `K_c`, the iterated derivative `(f_c^[n])'(z) = ∏_{k<n} 2·f_c^[k](z)`
(`hasStrictDerivAt_quadratic_iterate`) has modulus `≥ (2δ)^n` at every `z ∈ K_c`: the forward orbit
`f_c^[k] z` stays in `K_c` (`filledJulia_forward`), so each factor `‖2·f_c^[k] z‖ = 2‖f_c^[k] z‖ ≥ 2δ`.
This is the expansion estimate at the heart of the hyperbolicity of the disconnected Julia set: once the
orbit-mean of `2‖·‖` exceeds `1`, inverse branches contract and the nested depth-`n` cylinders shrink to
a Cantor set — the carrier of the unbounded-order dyadic monodromy that discharges `hDisc`. -/
theorem norm_deriv_iterate_filledJulia_ge {c : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hmin : ∀ z ∈ filledJulia c, δ ≤ ‖z‖) {z : ℂ} (hz : z ∈ filledJulia c) (n : ℕ) :
    (2 * δ) ^ n ≤ ‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ := by
  rw [norm_prod]
  have hterm : ∀ k ∈ Finset.range n, 2 * δ ≤ ‖2 * (quadratic c)^[k] z‖ := by
    intro k _
    rw [norm_mul, Complex.norm_two]
    have hk : (quadratic c)^[k] z ∈ filledJulia c := filledJulia_forward hz k
    have := hmin _ hk
    nlinarith [this]
  calc (2 * δ) ^ n = ∏ _k ∈ Finset.range n, (2 * δ) := by rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range n, ‖2 * (quadratic c)^[k] z‖ :=
        Finset.prod_le_prod (fun k _ => by positivity) hterm

end Bottcher

namespace Bottcher

open Complex Set

/-- **The derivative cocycle of the iterated quadratic.** The iterated-derivative product factors over
orbit segments: `(f_c^[N+M])'(z) = (f_c^[N])'(z) · (f_c^[M])'(f_c^[N] z)`. Splitting `range (N+M)` and
using `f_c^[N+k] z = f_c^[k](f_c^[N] z)`. This cocycle makes `N ↦ log min_{K_c}‖(f^[N])'‖`
SUPERADDITIVE (the second factor is evaluated at `f^[N] z ∈ K_c` by `filledJulia_forward`), so by Fekete
its average converges to the minimal Lyapunov exponent `Λ ≥ log(2δ)` — the structural backbone of the
hyperbolicity of the disconnected Julia set that builds the shrinking depth-`k` Cantor cylinders. -/
theorem deriv_iterate_quadratic_cocycle (c : ℂ) (N M : ℕ) (z : ℂ) :
    (∏ k ∈ Finset.range (N + M), 2 * (quadratic c)^[k] z)
      = (∏ k ∈ Finset.range N, 2 * (quadratic c)^[k] z)
        * (∏ k ∈ Finset.range M, 2 * (quadratic c)^[k] ((quadratic c)^[N] z)) := by
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [← Function.iterate_add_apply, Nat.add_comm N k]

/-- **Multiplicativity of the iterated expansion along the orbit.** The `(N+M)`-fold expansion modulus
at `z` is the product of the `N`-fold expansion at `z` and the `M`-fold expansion at `f_c^[N] z`. With
`f_c^[N] z ∈ K_c` (forward-invariance) this is the multiplicative Fekete structure underlying
hyperbolicity on `K_c`. -/
theorem norm_deriv_iterate_filledJulia_mul {c : ℂ} {z : ℂ} (N M : ℕ) :
    ‖∏ k ∈ Finset.range (N + M), 2 * (quadratic c)^[k] z‖
      = ‖∏ k ∈ Finset.range N, 2 * (quadratic c)^[k] z‖
        * ‖∏ k ∈ Finset.range M, 2 * (quadratic c)^[k] ((quadratic c)^[N] z)‖ := by
  rw [deriv_iterate_quadratic_cocycle, norm_mul]

end Bottcher

namespace Bottcher

open Complex Set

/-- **One expanding iterate bootstraps to uniform expansion on `K_c`.** If at some level `N₀` the
iterated derivative is uniformly `≥ L ≥ 0` on all of `K_c`, then at every multiple `m·N₀` it is `≥ L^m`.
Pure consequence of the derivative cocycle (`norm_deriv_iterate_filledJulia_mul`) and forward-invariance
(`filledJulia_forward`): induct on `m`, splitting `(m+1)·N₀ = m·N₀ + N₀` and evaluating the second
factor at `f_c^[m·N₀] z ∈ K_c`. This reduces full hyperbolicity of the disconnected Julia set to a
SINGLE expanding iterate: with `L > 1`, `L^m → ∞`, the inverse branches contract at a uniform geometric
rate, so the nested depth-`(m·N₀)` Cantor cylinders have diameter → 0 — the carrier of the
unbounded-order dyadic `φ_{c₁}`-monodromy of the disconnected case of `q62`. -/
theorem uniform_expansion_of_one_expanding_iterate {c : ℂ} {N₀ : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hexp : ∀ z ∈ filledJulia c, L ≤ ‖∏ k ∈ Finset.range N₀, 2 * (quadratic c)^[k] z‖)
    {z : ℂ} (hz : z ∈ filledJulia c) (m : ℕ) :
    L ^ m ≤ ‖∏ k ∈ Finset.range (m * N₀), 2 * (quadratic c)^[k] z‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hfwd : (quadratic c)^[m * N₀] z ∈ filledJulia c := filledJulia_forward hz (m * N₀)
    have hsplit : (m + 1) * N₀ = m * N₀ + N₀ := by ring
    rw [hsplit, norm_deriv_iterate_filledJulia_mul, pow_succ]
    have h1 : L ^ m ≤ ‖∏ k ∈ Finset.range (m * N₀), 2 * (quadratic c)^[k] z‖ := ih
    have h2 : L ≤ ‖∏ k ∈ Finset.range N₀, 2 * (quadratic c)^[k] ((quadratic c)^[m * N₀] z)‖ :=
      hexp _ hfwd
    exact mul_le_mul h1 h2 hL (norm_nonneg _)

/-- **Unconditional expansion on the disconnected filled Julia set.** For disconnected `c` there is a
rate `δ > 0` (the minimal modulus on `K_c`, positive because `0 ∉ K_c`) with `‖(f_c^[n])'(z)‖ ≥ (2δ)^n`
for every `z ∈ K_c` and every `n`. Self-contained combination of `exists_min_norm_filledJulia_pos` and
`norm_deriv_iterate_filledJulia_ge`. When `2δ > 1` (e.g. `K_c` far from `0`, as for large `‖c‖`) this is
already genuine uniform expansion; the general case feeds `uniform_expansion_of_one_expanding_iterate`
once a single iterate `(f_c^[N₀])'` is shown `> 1` on `K_c` (the Mañé step). -/
theorem disconnected_expansion {c : ℂ} (hc : Disconnected c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ filledJulia c, ∀ n : ℕ,
      (2 * δ) ^ n ≤ ‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ := by
  obtain ⟨δ, hδ, hmin⟩ := exists_min_norm_filledJulia_pos hc
  exact ⟨δ, hδ, fun z hz n => norm_deriv_iterate_filledJulia_ge hδ hmin hz n⟩

end Bottcher

namespace Bottcher

open Complex Set Metric

/-- **`K_c` is uniformly separated from the whole critical orbit (disconnected `c`).** There is `ρ > 0`
with `ρ ≤ ‖z − f_c^[k] 0‖` for every `z ∈ K_c` and every `k`. The forward critical orbit avoids `K_c`
(`not_mem_filledJulia_iterate`, since `0 ∉ K_c`) and escapes: past the first escape time `N` the orbit
has modulus `≥ ‖w‖ > R_c = max 2‖c‖ ≥` the radius bounding `K_c` (`filledJulia_subset_closedBall`,
`norm_iterate_ge`), so the tail is `≥ ‖w‖ − R_c` from `K_c`; the finitely many early points `k < N` are
each at positive `infDist` from the compact `K_c`. This uniform gap keeps the Poincaré density of
`ℂ ∖ (critical orbit)` finite on `K_c` — the input to the Mañé hyperbolicity that builds the shrinking
depth-`k` Cantor cylinders of the disconnected case (so that the inverse branches contract uniformly and
a single expanding iterate exists, feeding `uniform_expansion_of_one_expanding_iterate`). -/
theorem exists_dist_filledJulia_critical_orbit_pos {c : ℂ} (hc : Disconnected c) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ filledJulia c, ∀ k : ℕ, ρ ≤ ‖z - (quadratic c)^[k] 0‖ := by
  have h0 : (0 : ℂ) ∉ filledJulia c := (disconnected_iff_zero_not_mem c).mp hc
  rcases (filledJulia c).eq_empty_or_nonempty with hemp | hKne
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    rw [hemp] at hz; simp only [Set.mem_empty_iff_false] at hz
  set Rc : ℝ := max 2 ‖c‖ with hRc
  have hRcpos : 0 < Rc := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hbound : ∀ z ∈ filledJulia c, ‖z‖ ≤ Rc := by
    intro z hz
    have := filledJulia_subset_closedBall c hz
    rwa [mem_closedBall, dist_zero_right] at this
  obtain ⟨N, hN⟩ := exists_orbit_gt h0 Rc
  set w : ℂ := (quadratic c)^[N] 0 with hw
  have hwRc : Rc < ‖w‖ := hN
  have hcw : ‖c‖ ≤ ‖w‖ := le_trans (le_max_right 2 ‖c‖) (le_of_lt hwRc)
  have h2w : 2 < ‖w‖ := lt_of_le_of_lt (le_max_left 2 ‖c‖) hwRc
  have htail : ∀ k, N ≤ k → ‖w‖ ≤ ‖(quadratic c)^[k] 0‖ := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [Nat.add_comm, Function.iterate_add_apply, ← hw]
    exact norm_iterate_ge hcw h2w j
  have hKclosed : IsClosed (filledJulia c) := isClosed_filledJulia c
  have hearly : ∀ k < N, 0 < Metric.infDist ((quadratic c)^[k] 0) (filledJulia c) := by
    intro k _
    exact (hKclosed.notMem_iff_infDist_pos hKne).mp (not_mem_filledJulia_iterate h0 k)
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · exfalso
    have hw0 : w = 0 := by rw [hw, hN0]; rfl
    rw [hw0, norm_zero] at hwRc
    linarith [hRcpos]
  · have hne : (Finset.range N).Nonempty := Finset.nonempty_range_iff.mpr hNpos.ne'
    set m : ℝ := (Finset.range N).inf' hne
      (fun k => Metric.infDist ((quadratic c)^[k] 0) (filledJulia c)) with hm
    have hmpos : 0 < m := by
      rw [hm, Finset.lt_inf'_iff]
      exact fun k hk => hearly k (Finset.mem_range.mp hk)
    refine ⟨min (‖w‖ - Rc) m, lt_min (by linarith) hmpos, ?_⟩
    intro z hz k
    rcases lt_or_ge k N with hkN | hkN
    · have h1 : m ≤ Metric.infDist ((quadratic c)^[k] 0) (filledJulia c) :=
        Finset.inf'_le _ (Finset.mem_range.mpr hkN)
      have h2 : Metric.infDist ((quadratic c)^[k] 0) (filledJulia c) ≤ dist ((quadratic c)^[k] 0) z :=
        Metric.infDist_le_dist_of_mem hz
      rw [dist_comm, dist_eq_norm] at h2
      exact le_trans (min_le_right _ _) (le_trans h1 h2)
    · have hge : ‖w‖ ≤ ‖(quadratic c)^[k] 0‖ := htail k hkN
      have hzle : ‖z‖ ≤ Rc := hbound z hz
      have hrev : ‖(quadratic c)^[k] 0‖ - ‖z‖ ≤ ‖z - (quadratic c)^[k] 0‖ := by
        rw [norm_sub_rev]; exact norm_sub_norm_le _ _
      exact le_trans (min_le_left _ _) (by linarith)

end Bottcher

namespace Bottcher

open Complex Set Metric

/-- **Local expansion from an inverse-branch contraction (Schwarz–Pick engine).** If a holomorphic
right inverse `g` of `f` (`f ∘ g = id` on `ball b R₁`) sends that disk into the smaller
`closedBall (g b) R₂`, then `f` EXPANDS at `z = g b`: `R₁ / R₂ ≤ ‖f'(z)‖`. Schwarz
(`Complex.norm_deriv_le_div_of_mapsTo_ball`) gives `‖g'(b)‖ ≤ R₂/R₁`; the chain rule on `f ∘ g = id`
gives `f'(z)·g'(b) = 1`, so `‖f'(z)‖ = 1/‖g'(b)‖ ≥ R₁/R₂`. This is the engine of the Mañé step for the
disconnected Julia set: at depth `n` the inverse branch of `f_c^[n]` over a fixed-radius disk (radius =
the postcritical gap `ρ`, `exists_dist_filledJulia_critical_orbit_pos`) lands in a disk whose radius → 0,
so `f_c^[n]` expands by the diameter ratio → one expanding iterate, feeding
`uniform_expansion_of_one_expanding_iterate`. -/
theorem expansion_of_inverse_branch {f g : ℂ → ℂ} {b z : ℂ} {R₁ R₂ : ℝ}
    (hg : DifferentiableOn ℂ g (Metric.ball b R₁))
    (hgz : g b = z)
    (hinv : Set.EqOn (f ∘ g) id (Metric.ball b R₁))
    (hmaps : Set.MapsTo g (Metric.ball b R₁) (Metric.closedBall z R₂))
    (hf : DifferentiableAt ℂ f z) (hR1 : 0 < R₁) (hR2 : 0 < R₂) :
    R₁ / R₂ ≤ ‖deriv f z‖ := by
  have hbmem : b ∈ Metric.ball b R₁ := Metric.mem_ball_self hR1
  have hgb : DifferentiableAt ℂ g b :=
    (hg b hbmem).differentiableAt (Metric.isOpen_ball.mem_nhds hbmem)
  have hfgb : DifferentiableAt ℂ f (g b) := hgz ▸ hf
  have hev : (f ∘ g) =ᶠ[nhds b] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hbmem] with w hw using hinv hw
  have hcomp : deriv (f ∘ g) b = deriv f (g b) * deriv g b :=
    (hfgb.hasDerivAt.comp b hgb.hasDerivAt).deriv
  have hone : deriv (f ∘ g) b = 1 := by rw [hev.deriv_eq]; simp
  rw [hgz] at hcomp
  have hprod : deriv f z * deriv g b = 1 := by rw [← hcomp, hone]
  have hmaps' : Set.MapsTo g (Metric.ball b R₁) (Metric.closedBall (g b) R₂) := by
    rw [hgz]; exact hmaps
  have hschwarz : ‖deriv g b‖ ≤ R₂ / R₁ := Complex.norm_deriv_le_div_of_mapsTo_ball hg hmaps' hR1
  have hnz : deriv g b ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod; exact one_ne_zero hprod.symm
  have hnorm1 : ‖deriv f z‖ * ‖deriv g b‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  have hschwarz' : ‖deriv g b‖ * R₁ ≤ R₂ := (le_div_iff₀ hR1).mp hschwarz
  rw [div_le_iff₀ hR2]
  calc R₁ = (‖deriv f z‖ * ‖deriv g b‖) * R₁ := by rw [hnorm1, one_mul]
    _ = ‖deriv f z‖ * (‖deriv g b‖ * R₁) := by ring
    _ ≤ ‖deriv f z‖ * R₂ := mul_le_mul_of_nonneg_left hschwarz' (norm_nonneg _)

end Bottcher

namespace Bottcher

open Complex Set Metric

/-- **Expansion of the iterate from a shrinking inverse branch (dynamical Schwarz bridge).** If `g` is a
holomorphic inverse branch of `f_c^[n]` on `ball b R₁` (`f_c^[n] ∘ g = id`) with `g b = z`, landing in
`closedBall z R₂`, then `R₁ / R₂ ≤ ‖∏_{k<n} 2·f_c^[k] z‖` (`= ‖(f_c^[n])'(z)‖`). Specializes
`expansion_of_inverse_branch` to `f = f_c^[n]`, identifying `deriv (f_c^[n]) z` with the orbit-product
(`hasStrictDerivAt_quadratic_iterate`). So once the depth-`n` inverse-branch image radius `R₂^{(n)}` is
shown to make `R₁/R₂^{(n)} > 1` for some `n` (the shrinking that uniform hyperbolicity provides — needing
univalent-function/Koebe or hyperbolic-metric infrastructure), this feeds
`uniform_expansion_of_one_expanding_iterate` to give the unbounded-order dyadic monodromy of the
disconnected case. -/
theorem norm_deriv_iterate_ge_of_inverse_branch {c : ℂ} {n : ℕ} {g : ℂ → ℂ} {b z : ℂ} {R₁ R₂ : ℝ}
    (hg : DifferentiableOn ℂ g (Metric.ball b R₁))
    (hgz : g b = z)
    (hinv : Set.EqOn ((quadratic c)^[n] ∘ g) id (Metric.ball b R₁))
    (hmaps : Set.MapsTo g (Metric.ball b R₁) (Metric.closedBall z R₂))
    (hR1 : 0 < R₁) (hR2 : 0 < R₂) :
    R₁ / R₂ ≤ ‖∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z‖ := by
  have hfdiff : DifferentiableAt ℂ ((quadratic c)^[n]) z :=
    (hasStrictDerivAt_quadratic_iterate c n z).hasDerivAt.differentiableAt
  have hderiv : deriv ((quadratic c)^[n]) z = ∏ k ∈ Finset.range n, 2 * (quadratic c)^[k] z :=
    (hasStrictDerivAt_quadratic_iterate c n z).hasDerivAt.deriv
  have h := expansion_of_inverse_branch hg hgz hinv hmaps hfdiff hR1 hR2
  rwa [hderiv] at h

end Bottcher
