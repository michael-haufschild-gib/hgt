import GaloisForLFunctions.RHTower.DeckIncompleteEisenstein

/-!
# The cuspidal carrier is cut out by incomplete Eisenstein series

A finite-deck `L²` vector `f` is cuspidal iff it is fixed by the central deck action and orthogonal
to every incomplete Eisenstein series `E(· | ψ, v)` (`ψ` a height profile, `ρ(T)v = v`).

* By unfolding, `⟨E(· | ψ, v), G⟩ = 2∫_0^∞ y⁻² \bar ψ(y) h_v(y) dy` for continuous deck-equivariant
  `G`, with the horocycle average `h_v(y) = ∫_0^1 ⟨v, G(x + iy)⟩ dx`.
* For the orbit vector `v_q = Σ_{k ≤ N} ρ(T^{-k}) e_q`, `h_{v_q}(y) = ∫_0^{N+1} G(x + iy)_q dx` is the
  level horocycle average of the coordinate `q`; for general `T`-fixed `v`, `(N+1) h_v(y)` is a
  combination of the level horocycle averages.  Hence `G` is cusp-zero iff all `h_v` vanish.
* A continuous `h` on `(0, ∞)` with `∫ y⁻² \bar ψ h = 0` for all height profiles vanishes
  (test with `ψ = y² h · heightTent`).
* Density: for central `f` orthogonal to all `E(· | ψ, v)`, the point-pair average `L_φ f` pairs
  with `E(· | ψ, v)` as `f` pairs with `E(· | ψ̃, v)`, so it is cusp-zero and lies in the cuspidal
  pre-domain; the approximate identity `L_φ f → f` puts `f` in the closed cuspidal carrier.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology EisensteinSeries
open scoped MatrixGroups ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-! ## A fundamental lemma on `(0, ∞)` -/

theorem continuous_of_continuousOn_Ioi {E : Type*} [TopologicalSpace E] [Zero E] {f : ℝ → E}
    {c : ℝ} (hc : 0 < c) (hf : ContinuousOn f (Ioi 0)) (h0 : ∀ y, y < c → f y = 0) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  rcases lt_or_ge 0 y with hy | hy
  · exact hf.continuousAt (Ioi_mem_nhds hy)
  · have h : f =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (lt_of_le_of_lt hy hc)] with t ht
      exact h0 t ht
    exact continuousAt_const.congr h.symm

/-- The heightTent `max(0, y₀/2 - |y - y₀|)`. -/
def heightTent (y₀ y : ℝ) : ℝ := max 0 (y₀ / 2 - |y - y₀|)

theorem continuous_heightTent (y₀ : ℝ) : Continuous (heightTent y₀) :=
  continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).abs)

theorem heightTent_nonneg (y₀ y : ℝ) : 0 ≤ heightTent y₀ y := le_max_left _ _

theorem heightTent_self (y₀ : ℝ) (hy₀ : 0 < y₀) : heightTent y₀ y₀ = y₀ / 2 := by
  rw [heightTent, sub_self, abs_zero, sub_zero, max_eq_right (by linarith)]

theorem heightTent_eq_zero_of_lt {y₀ y : ℝ} (hy : y < y₀ / 2) : heightTent y₀ y = 0 := by
  rw [heightTent, max_eq_left]
  have : y₀ - y ≤ |y - y₀| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith

theorem heightTent_eq_zero_of_gt {y₀ y : ℝ} (hy : 3 * y₀ / 2 < y) : heightTent y₀ y = 0 := by
  rw [heightTent, max_eq_left]
  have h0 : 0 ≤ y - y₀ ∨ y - y₀ < 0 := le_or_gt 0 (y - y₀)
  rcases h0 with h0 | h0
  · rw [abs_of_nonneg h0]; linarith
  · rw [abs_of_neg h0]; linarith

/-- **Fundamental lemma.** A function continuous on `(0, ∞)` with
`∫_0^∞ y⁻² \bar ψ(y) h(y) dy = 0` for every height profile `ψ` vanishes on `(0, ∞)`. -/
theorem eq_zero_of_forall_heightProfile {h : ℝ → ℂ} (hc : ContinuousOn h (Ioi 0))
    (H : ∀ ψ : HeightProfile, ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ • (conj (ψ.toFun y) * h y) = 0)
    {y₀ : ℝ} (hy₀ : 0 < y₀) : h y₀ = 0 := by
  by_contra hne
  have hq := half_pos hy₀
  set f : ℝ → ℝ := fun y => heightTent y₀ y * ‖h y‖ ^ 2 with hfdef
  have hf0 : ∀ y, y < y₀ / 2 → f y = 0 := fun y hy => by
    simp only [hfdef, heightTent_eq_zero_of_lt hy, zero_mul]
  have hfc : Continuous f := continuous_of_continuousOn_Ioi hq
    ((continuous_heightTent y₀).continuousOn.mul (hc.norm.pow 2)) hf0
  let ψ : HeightProfile :=
    { toFun := fun y => ((heightTent y₀ y * y ^ 2 : ℝ) : ℂ) * h y
      lower := y₀ / 2
      upper := 3 * y₀ / 2
      lower_pos := hq
      lower_le_upper := by linarith
      continuous := continuous_of_continuousOn_Ioi hq
        (((Complex.continuous_ofReal.comp ((continuous_heightTent y₀).mul
          (continuous_pow 2))).continuousOn).mul hc)
        (fun y hy => by simp [heightTent_eq_zero_of_lt hy])
      eq_zero_of_lt := fun y hy => by simp [heightTent_eq_zero_of_lt hy]
      eq_zero_of_gt := fun y hy => by simp [heightTent_eq_zero_of_gt hy] }
  have h2 : ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ • (conj (ψ.toFun y) * h y) =
      ∫ y in Ioi (0 : ℝ), ((f y : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hy)
    simp only [ψ, hfdef]
    rw [map_mul, Complex.conj_ofReal, mul_assoc, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, Complex.real_smul]
    push_cast
    field_simp
  have hint : ∫ y in Ioi (0 : ℝ), f y = ∫ y, f y :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
      hf0 y (lt_of_le_of_lt (not_lt.1 hy) hq)
  have hsupp : HasCompactSupport f := HasCompactSupport.intro (K := Icc (y₀ / 2) (3 * y₀ / 2))
    isCompact_Icc fun y hy => by
      simp only [mem_Icc, not_and_or, not_le] at hy
      rcases hy with hy | hy
      · exact hf0 y hy
      · simp only [hfdef, heightTent_eq_zero_of_gt hy, zero_mul]
  have hpos : 0 < ∫ y, f y := hfc.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp
    (fun y => mul_nonneg (heightTent_nonneg _ _) (sq_nonneg _)) (x := y₀) (by
      simp only [hfdef, heightTent_self y₀ hy₀]
      exact mul_ne_zero (ne_of_gt hq) (pow_ne_zero 2 (norm_ne_zero_iff.2 hne)))
  have h3 := H ψ
  rw [h2, integral_complex_ofReal, hint] at h3
  exact (ne_of_gt hpos) (by exact_mod_cast h3)

/-! ## Horocycle averages -/

section Horocycle

open Classical

variable {G : ℍ → DeckSpace N} {y : ℝ}

theorem point_eq_mk (x y : ℝ) : SelbergMaassMean.point x y = ⟨x, y⟩ := by
  apply Complex.ext <;> simp [SelbergMaassMean.point]

theorem horoAverage_eq_intervalIntegral (v : DeckSpace N) (G : ℍ → DeckSpace N) (y : ℝ) :
    horoAverage v G y = ∫ x in (0 : ℝ)..1, ⟪v, G (ofComplex (SelbergMaassMean.point x y))⟫_ℂ := by
  rw [horoAverage, intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  simp only [point_eq_mk]

theorem ofComplex_point_re {x y : ℝ} (hy : 0 < y) : (ofComplex (SelbergMaassMean.point x y)).re = x := by
  rw [ofComplex_apply_of_im_pos (by simpa [SelbergMaassMean.point] using hy)]
  simp [SelbergMaassMean.point]

theorem ofComplex_point_im {x y : ℝ} (hy : 0 < y) : (ofComplex (SelbergMaassMean.point x y)).im = y := by
  rw [ofComplex_apply_of_im_pos (by simpa [SelbergMaassMean.point] using hy)]
  simp [SelbergMaassMean.point]

/-- Integer translation along a horocycle is the deck action of `T^k`. -/
theorem apply_ofComplex_point_add_int (hGe : deckEquivariant N G) (hy : 0 < y) (k : ℤ) (x : ℝ) :
    G (ofComplex (SelbergMaassMean.point (x + k) y)) =
      deckRho N (ModularGroup.T ^ k) (G (ofComplex (SelbergMaassMean.point x y))) := by
  rw [← hGe, modular_T_zpow_smul, vadd_eq_ofComplex_point, ofComplex_point_re hy,
    ofComplex_point_im hy, add_comm]

theorem continuousOn_horoAverage (hGc : Continuous G) (v : DeckSpace N) :
    ContinuousOn (horoAverage v G) (Ioi 0) := by
  have hH : Continuous fun z : ℍ => ∫ x in (0 : ℝ)..1, ⟪v, G ((x : ℝ) +ᵥ z)⟫_ℂ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (continuous_const.inner (hGc.comp (continuous_vadd_upper.comp continuous_swap))) 0 1
  have hp : Continuous fun y : ℝ => SelbergMaassMean.point 0 y := by
    unfold SelbergMaassMean.point
    fun_prop
  have hpt : ContinuousOn (fun y : ℝ => ofComplex (SelbergMaassMean.point 0 y)) (Ioi 0) :=
    continuousOn_ofComplex.comp hp.continuousOn fun y hy => by
      show 0 < (SelbergMaassMean.point 0 y).im
      simpa [SelbergMaassMean.point] using hy
  refine (hH.comp_continuousOn hpt).congr fun y hy => ?_
  rw [horoAverage_eq_intervalIntegral]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only
  rw [vadd_eq_ofComplex_point, ofComplex_point_re hy, ofComplex_point_im hy, add_zero]

/-- Elements of the level subgroup act trivially on the deck. -/
theorem deckRho_of_mem_Gamma {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma (N + 1))
    (v : DeckSpace N) : deckRho N g v = v := by
  letI : (CongruenceSubgroup.Gamma (N + 1)).Normal := CongruenceSubgroup.Gamma_normal (N + 1)
  have h1 : (QuotientGroup.mk g : Deck N) = 1 := (QuotientGroup.eq_one_iff g).mpr hg
  ext q
  change v (q * (QuotientGroup.mk g : Deck N)) = v q
  rw [h1, mul_one]

theorem deckRho_T_zpow_level (m : ℤ) (v : DeckSpace N) :
    deckRho N (ModularGroup.T ^ (((N + 1 : ℕ) : ℤ) * m)) v = v := by
  refine deckRho_of_mem_Gamma ?_ v
  simpa only [Int.natAbs_natCast] using
    CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma ((N + 1 : ℕ) : ℤ) _ (dvd_mul_right _ m)

/-- The level period of each coordinate along a horocycle. -/
theorem periodic_coordinate (hGe : deckEquivariant N G) (hy : 0 < y) (q : Deck N) :
    Function.Periodic (fun x => G (ofComplex (SelbergMaassMean.point x y)) q)
      ((N + 1 : ℕ) : ℝ) := by
  intro x
  have h := apply_ofComplex_point_add_int hGe hy (((N + 1 : ℕ) : ℤ) * 1) x
  rw [deckRho_T_zpow_level] at h
  simp only [mul_one, Int.cast_natCast] at h
  simp only
  rw [h]

/-- The orbit vector `v_q = Σ_{k ≤ N} ρ(T^{-k}) e_q`. -/
def deckOrbitVec (q : Deck N) : DeckSpace N :=
  ∑ k ∈ Finset.range (N + 1), deckRho N (ModularGroup.T ^ (-(k : ℤ))) (EuclideanSpace.single q 1)

theorem deckRho_T_orbitVec (q : Deck N) : deckRho N ModularGroup.T (deckOrbitVec q) = deckOrbitVec q := by
  unfold deckOrbitVec
  rw [map_sum, Finset.sum_range_succ', Finset.sum_range_succ]
  have hlast : deckRho N (ModularGroup.T ^ (-((N : ℕ) : ℤ))) (EuclideanSpace.single q 1) =
      deckRho N ModularGroup.T (deckRho N (ModularGroup.T ^ (-((0 : ℕ) : ℤ)))
        (EuclideanSpace.single q 1)) := by
    rw [← deckRho_mul, ← zpow_one_add]
    have : -((N : ℕ) : ℤ) = (1 + -((0 : ℕ) : ℤ)) + ((N + 1 : ℕ) : ℤ) * (-1) := by push_cast; ring
    rw [this, zpow_add, deckRho_mul, deckRho_T_zpow_level]
  rw [hlast]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← deckRho_mul, ← zpow_one_add,
    show (1 : ℤ) + -((k + 1 : ℕ) : ℤ) = -(k : ℤ) by push_cast; ring]

theorem inner_orbitVec (q : Deck N) (w : DeckSpace N) :
    ⟪deckOrbitVec q, w⟫_ℂ = ∑ k ∈ Finset.range (N + 1), deckRho N (ModularGroup.T ^ (k : ℤ)) w q := by
  unfold deckOrbitVec
  rw [sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zpow_neg, deckRho_inv, ← (deckRho N (ModularGroup.T ^ (k : ℤ))).inner_map_map,
    LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.inner_single_left, map_one, one_mul]

/-- The orbit horocycle average is the level horocycle average of the coordinate `q`. -/
theorem horoAverage_orbitVec (hGc : Continuous G) (hGe : deckEquivariant N G) (hy : 0 < y)
    (q : Deck N) :
    horoAverage (deckOrbitVec q) G y =
      ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), G (ofComplex (SelbergMaassMean.point x y)) q := by
  set F : ℝ → ℂ := fun x => G (ofComplex (SelbergMaassMean.point x y)) q with hF
  have hFc : Continuous F := (PiLp.continuous_apply 2 _ q).comp
    (hGc.comp (MaassFiniteDeckDirichlet.continuous_ofComplex_point hy))
  rw [horoAverage_eq_intervalIntegral]
  have hpt : ∀ x : ℝ, ⟪deckOrbitVec q, G (ofComplex (SelbergMaassMean.point x y))⟫_ℂ =
      ∑ k ∈ Finset.range (N + 1), F (x + (k : ℤ)) := by
    intro x
    rw [inner_orbitVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hF]
    rw [apply_ofComplex_point_add_int hGe hy]
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum (f := fun (k : ℕ) (x : ℝ) => F (x + ((k : ℤ) : ℝ)))
    fun k _ => (hFc.comp (continuous_add_const _)).intervalIntegrable _ _]
  have hk : ∀ k ∈ Finset.range (N + 1), ∫ x in (0 : ℝ)..1, F (x + (k : ℤ)) =
      ∫ x in ((k : ℕ) : ℝ)..(((k + 1 : ℕ) : ℕ) : ℝ), F x := by
    intro k _
    rw [intervalIntegral.integral_comp_add_right]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hk, intervalIntegral.sum_integral_adjacent_intervals
    fun k _ => hFc.intervalIntegrable _ _]
  simp

/-- For `T`-fixed `v`, `(N+1) h_v(y)` combines the level horocycle averages. -/
theorem natCast_mul_horoAverage (hGc : Continuous G) (hGe : deckEquivariant N G) (hy : 0 < y)
    {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) :
    ((N + 1 : ℕ) : ℂ) * horoAverage v G y = ∑ r : Deck N, conj (v r) *
      ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), G (ofComplex (SelbergMaassMean.point x y)) r := by
  set g : ℝ → ℂ := fun x => ⟪v, G (ofComplex (SelbergMaassMean.point x y))⟫_ℂ with hg
  have hgc : Continuous g := continuous_const.inner
    (hGc.comp (MaassFiniteDeckDirichlet.continuous_ofComplex_point hy))
  have hper : Function.Periodic g 1 := by
    intro x
    simp only [hg]
    have h := apply_ofComplex_point_add_int hGe hy 1 x
    simp only [Int.cast_one, zpow_one] at h
    rw [h]
    conv_lhs => rw [← hv]
    exact (deckRho N ModularGroup.T).inner_map_map v _
  have h1 := hper.intervalIntegral_add_zsmul_eq ((N + 1 : ℕ) : ℤ) 0
    fun t₁ t₂ => hgc.intervalIntegrable _ _
  simp only [zero_add, zsmul_eq_mul, mul_one, Int.cast_natCast] at h1
  rw [horoAverage_eq_intervalIntegral, ← h1]
  simp only [hg, PiLp.inner_apply, RCLike.inner_apply]
  rw [intervalIntegral.integral_finsetSum (f := fun (r : Deck N) (x : ℝ) =>
      (G (ofComplex (SelbergMaassMean.point x y))).ofLp r * conj (v.ofLp r))
    fun r _ => (((PiLp.continuous_apply 2 _ r).comp
      (hGc.comp (MaassFiniteDeckDirichlet.continuous_ofComplex_point hy))).intervalIntegrable
        _ _).mul_const _]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [intervalIntegral.integral_mul_const, mul_comm]

/-- Cusp-zero from vanishing orbit horocycle averages. -/
theorem levelCuspZero_of_horoAverage (hGc : Continuous G) (hGe : deckEquivariant N G)
    (h : ∀ q : Deck N, ∀ y > 0, horoAverage (deckOrbitVec q) G y = 0) : levelCuspZero N G := by
  intro q y hy a
  rw [(periodic_coordinate hGe hy q).intervalIntegral_add_eq a 0, zero_add,
    ← horoAverage_orbitVec hGc hGe hy q, h q y hy]

/-- Vanishing horocycle averages for cusp-zero `G` and every `T`-fixed `v`. -/
theorem horoAverage_eq_zero (hGc : Continuous G) (hGe : deckEquivariant N G)
    (h0 : levelCuspZero N G) {v : DeckSpace N} (hv : deckRho N ModularGroup.T v = v) (hy : 0 < y) :
    horoAverage v G y = 0 := by
  have h := natCast_mul_horoAverage hGc hGe hy hv
  have hz : ∀ r : Deck N,
      ∫ x in (0 : ℝ)..((N + 1 : ℕ) : ℝ), G (ofComplex (SelbergMaassMean.point x y)) r = 0 := by
    intro r
    have := h0 r hy 0
    simpa using this
  simp only [hz, mul_zero, Finset.sum_const_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast Nat.succ_ne_zero N)

end Horocycle

/-! ## Orthogonality and density -/

theorem toDeckL2_mem_cuspidalL2Closure (F : cuspidalFormPreDomain N) :
    toDeckL2 (F : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp F) ∈ cuspidalL2Closure N :=
  subset_closure ⟨toCuspidalFormDomain N F, rfl⟩

theorem incEisL2_mem_deckCentralFixedL2 (ψ : HeightProfile) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) : incEisL2 ψ v ∈ deckCentralFixedL2 N :=
  toDeckL2_mem_deckCentralFixedL2 (deckEquivariant_incEis hv) (ψ.memLp_incEis v)

/-- **Cuspidal vectors are orthogonal to incomplete Eisenstein series.** -/
theorem inner_incEisL2_eq_zero_of_mem (ψ : HeightProfile) {v : DeckSpace N}
    (hv : deckRho N ModularGroup.T v = v) {f : DeckL2 N} (hf : f ∈ cuspidalL2Closure N) :
    ⟪incEisL2 ψ v, f⟫_ℂ = 0 := by
  have hclosed : IsClosed {f : DeckL2 N | ⟪incEisL2 ψ v, f⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hbase : ∀ G : cuspidalFormPreDomain N,
      ⟪incEisL2 ψ v, toDeckL2 (G : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp G)⟫_ℂ = 0 := by
    intro G
    have hGc : Continuous (G : ℍ → DeckSpace N) :=
      continuous_of_isChartC1 (cuspidalFormPreDomain.c1 G)
    have hGe : deckEquivariant N (G : ℍ → DeckSpace N) :=
      fun A z => (cuspidalFormPreDomain.toFormPreDomain N G).2.2.1 A z
    have h := inner_incEisL2 ψ hv
      (g := toDeckL2 (G : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp G))
      (MemLp.coeFn_toLp (cuspidalFormPreDomain.memLp G)) hGc hGe
    rw [h, setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℂ)) fun y hy => by
        rw [horoAverage_eq_zero hGc hGe (cuspidalFormPreDomain.cusp_zero G) hv hy, mul_zero,
          smul_zero]]
    simp
  have hT : (cuspidalFormDomainClosure N : Set (FormTriple N)) ⊆
      (fun x : FormTriple N => x.ofLp 0) ⁻¹' {f : DeckL2 N | ⟪incEisL2 ψ v, f⟫_ℂ = 0} := by
    refine closure_minimal ?_ (hclosed.preimage (PiLp.continuous_apply 2 _ 0))
    rintro _ ⟨G, rfl⟩
    exact hbase G
  have hU : (cuspidalL2Closure N : Set (DeckL2 N)) ⊆ {f : DeckL2 N | ⟪incEisL2 ψ v, f⟫_ℂ = 0} := by
    refine closure_minimal ?_ hclosed
    rintro _ ⟨w, rfl⟩
    exact hT w.2
  exact hU hf

/-- A point-pair average of a vector orthogonal to all incomplete Eisenstein series lies in the
cuspidal carrier. -/
theorem SmoothProfile.op_mem_cuspidalL2Closure (P : SmoothProfile) {f : DeckL2 N}
    (horth : ∀ (ψ : HeightProfile) (v : DeckSpace N), deckRho N ModularGroup.T v = v →
      ⟪incEisL2 ψ v, f⟫_ℂ = 0) : P.pp.op N f ∈ cuspidalL2Closure N := by
  set G : ℍ → DeckSpace N := ppApply P.pp.toFun ⇑f with hGdef
  have hmem : G ∈ formPreDomain N := P.pp.ppApply_mem f
  have hGc : Continuous G := continuous_ppApply P.pp.differentiable.continuous P.pp.abs_le
    P.pp.support (Lp.memLp f)
  have hGe : deckEquivariant N G := fun A z => ppApply_smul_point P.pp.support _ A z
  have hcusp : levelCuspZero N G := by
    refine levelCuspZero_of_horoAverage hGc hGe fun q y hy => ?_
    refine eq_zero_of_forall_heightProfile (continuousOn_horoAverage hGc _) (fun ψ => ?_) hy
    have h1 := inner_incEisL2 ψ (deckRho_T_orbitVec q) (P.pp.op_coeFn f) hGc hGe
    have hs : ⟪incEisL2 ψ (deckOrbitVec q), P.pp.op N f⟫_ℂ =
        ⟪P.pp.op N (incEisL2 ψ (deckOrbitVec q)), f⟫_ℂ :=
      ((P.pp.op_isSymmetric N) (incEisL2 ψ (deckOrbitVec q)) f).symm
    rw [hs, PairProfile.op_incEisL2 P.pp ψ (deckRho_T_orbitVec q),
      horth _ _ (deckRho_T_orbitVec q)] at h1
    exact (mul_eq_zero.1 h1.symm).resolve_left two_ne_zero
  have hop : P.pp.op N f = toDeckL2 G (formPreDomain.memLp ⟨G, hmem⟩) := by
    apply Lp.ext
    filter_upwards [P.pp.op_coeFn f, MemLp.coeFn_toLp (formPreDomain.memLp ⟨G, hmem⟩)] with z h1 h2
    rw [h1, toDeckL2, h2]
  rw [hop]
  exact toDeckL2_mem_cuspidalL2Closure ⟨G, hmem, hcusp⟩

/-- **Density.** A central finite-deck `L²` vector orthogonal to every incomplete Eisenstein
series is cuspidal. -/
theorem mem_cuspidalL2Closure_of_forall_inner_incEisL2 {f : DeckL2 N}
    (hf : f ∈ deckCentralFixedL2 N)
    (horth : ∀ (ψ : HeightProfile) (v : DeckSpace N), deckRho N ModularGroup.T v = v →
      ⟪incEisL2 ψ v, f⟫_ℂ = 0) : f ∈ cuspidalL2Closure N := by
  have hclosed : IsClosed (cuspidalL2Closure N : Set (DeckL2 N)) :=
    Submodule.isClosed_topologicalClosure _
  suffices h : f ∈ closure (cuspidalL2Closure N : Set (DeckL2 N)) by
    rwa [hclosed.closure_eq] at h
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨R₀, hR₀, happ⟩ := exists_radius_approxIdentity (⟨f, hf⟩ : deckCentralFixedL2 N)
    (half_pos hε)
  obtain ⟨P, hPR, hP0, hPm⟩ := exists_smoothUnitProfile hR₀
  refine ⟨P.pp.op N f, P.op_mem_cuspidalL2Closure horth, ?_⟩
  have h1 := happ P.pp.differentiable.continuous P.pp.abs_le P.pp.radius_nonneg P.pp.support hP0
    hPm hPR
  change ‖P.pp.op N f - f‖ ≤ ε / 2 at h1
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- **The cuspidal carrier is cut out by incomplete Eisenstein series**:
`CuspidalL2 = {f central : ⟨E(· | ψ, v), f⟩ = 0 for all ψ and all T-fixed v}`. -/
theorem mem_cuspidalL2Closure_iff (f : DeckL2 N) :
    f ∈ cuspidalL2Closure N ↔ f ∈ deckCentralFixedL2 N ∧
      ∀ (ψ : HeightProfile) (v : DeckSpace N), deckRho N ModularGroup.T v = v →
        ⟪incEisL2 ψ v, f⟫_ℂ = 0 :=
  ⟨fun hf => ⟨cuspidalL2Closure_le_deckCentralFixedL2 hf,
      fun ψ _ hv => inner_incEisL2_eq_zero_of_mem ψ hv hf⟩,
    fun h => mem_cuspidalL2Closure_of_forall_inner_incEisL2 h.1 h.2⟩

end

end GaloisForLFunctions.RHTower.DeckPointPair
