import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModeMean
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleBridge

/-!
# The mean occupation of a single mode

The occupation law of one prime-depth mode is geometric with ratio `r`, so its mean is `r/(1−r)`.
Stated as a lower Lebesgue integral this is unconditional: no integrability hypothesis is needed,
and the value is finite because `r < 1`.

This is the atom of the gas-expectation layer: the socle observable `log|soc A|` is the
mode-additive functional `∑_{(p,j)} A(p,j)·log p`, so its expectation is assembled from these
single-mode means.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

namespace AbelianZetaParameters

theorem tsum_natCast_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, (n : ℝ) * r ^ n * (1 - r)) = r / (1 - r) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hgeom : (∑' n : ℕ, (n : ℝ) * r ^ n) = r / (1 - r) ^ 2 :=
    tsum_coe_mul_geometric_of_norm_lt_one hnorm
  have hden : (1 : ℝ) - r ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact absurd h.symm hr1.ne
  calc (∑' n : ℕ, (n : ℝ) * r ^ n * (1 - r))
      = (∑' n : ℕ, (n : ℝ) * r ^ n) * (1 - r) := by rw [tsum_mul_right]
    _ = r / (1 - r) ^ 2 * (1 - r) := by rw [hgeom]
    _ = r / (1 - r) := by
        field_simp

theorem summable_natCast_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => (n : ℝ) * r ^ n * (1 - r) := by
  have hnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  simp only [pow_one] at h
  exact h.mul_right _

/-- **The mean occupation of a mode.**  The geometric mode law has mean `r/(1−r)`. -/
theorem lintegral_modeLaw (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    ∫⁻ n, (n : ℝ≥0∞) ∂(θ.modeLaw m)
      = ENNReal.ofReal (θ.ratio m / (1 - θ.ratio m)) := by
  classical
  have hr0 : 0 ≤ θ.ratio m := θ.ratio_nonneg m
  have hr1 : θ.ratio m < 1 := θ.ratio_lt_one m
  have hcount := lintegral_countable' (μ := θ.modeLaw m) (f := fun n : ℕ => (n : ℝ≥0∞))
  rw [hcount]
  have hterm : ∀ n : ℕ, (n : ℝ≥0∞) * θ.modeLaw m {n}
      = ENNReal.ofReal ((n : ℝ) * θ.ratio m ^ n * (1 - θ.ratio m)) := by
    intro n
    rw [θ.modeLaw_singleton m n, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
      (Nat.cast_nonneg n)]
    congr 1
    ring
  rw [tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg
    (fun n => by positivity) (summable_natCast_mul_geometric hr0 hr1),
    tsum_natCast_mul_geometric hr0 hr1]

/-! ## Expectations under the gas -/

/-- **The mean occupation of a mode under the gas.** -/
theorem lintegral_gasMeasure_eval (θ : AbelianZetaParameters) (m : AbelianZetaMode) :
    ∫⁻ k, ((k m : ℕ) : ℝ≥0∞) ∂θ.gasMeasure
      = ENNReal.ofReal (θ.ratio m / (1 - θ.ratio m)) := by
  have hmeasm : Measurable fun k : AbelianZetaMode → ℕ => ((k m : ℕ) : ℝ≥0∞) :=
    Measurable.comp measurable_from_top (measurable_pi_apply m)
  have hmap : θ.gasMeasure.map (fun k : AbelianZetaMode → ℕ => k m) = θ.modeLaw m := by
    rw [AbelianZetaParameters.gasMeasure]
    exact MeasureTheory.Measure.infinitePi_map_eval (μ := θ.modeLaw) m
  have hlint : ∫⁻ n, (n : ℝ≥0∞) ∂(θ.gasMeasure.map (fun k : AbelianZetaMode → ℕ => k m))
      = ∫⁻ k, ((k m : ℕ) : ℝ≥0∞) ∂θ.gasMeasure :=
    lintegral_map measurable_from_top (measurable_pi_apply m)
  rw [← hlint, hmap, θ.lintegral_modeLaw m]

/-- **The expectation of a mode-additive observable.**  Every nonnegative mode-additive functional
integrates coefficientwise against the single-mode means. -/
theorem lintegral_gasMeasure_tsum (θ : AbelianZetaParameters) (c : AbelianZetaMode → ℝ≥0∞) :
    ∫⁻ k, (∑' m : AbelianZetaMode, c m * ((k m : ℕ) : ℝ≥0∞)) ∂θ.gasMeasure
      = ∑' m : AbelianZetaMode, c m * ENNReal.ofReal (θ.ratio m / (1 - θ.ratio m)) := by
  have hmeasm : ∀ m : AbelianZetaMode,
      Measurable fun k : AbelianZetaMode → ℕ => ((k m : ℕ) : ℝ≥0∞) :=
    fun m => Measurable.comp measurable_from_top (measurable_pi_apply m)
  have hmeas : ∀ m : AbelianZetaMode,
      AEMeasurable (fun k : AbelianZetaMode → ℕ => c m * ((k m : ℕ) : ℝ≥0∞)) θ.gasMeasure :=
    fun m => ((hmeasm m).const_mul (c m)).aemeasurable
  rw [lintegral_tsum hmeas]
  refine tsum_congr fun m => ?_
  rw [lintegral_const_mul (c m) (hmeasm m), lintegral_gasMeasure_eval θ m]

/-! ## The socle expectation -/

/-- The expectation of the socle observable `log|soc A| = ∑_{(p,j)} A(p,j)·log p`. -/
def socleExpectation (θ : AbelianZetaParameters) : ℝ≥0∞ :=
  ∫⁻ k, (∑' m : AbelianZetaMode,
      ENNReal.ofReal (Real.log ((m.1 : ℕ) : ℝ)) * ((k m : ℕ) : ℝ≥0∞)) ∂θ.gasMeasure

/-- **The socle expectation groups by prime.** -/
theorem socleExpectation_eq (θ : AbelianZetaParameters) :
    socleExpectation θ
      = ∑' p : Nat.Primes, ENNReal.ofReal (Real.log ((p : ℕ) : ℝ))
        * ∑' j : ℕ, ENNReal.ofReal (θ.ratio (p, j) / (1 - θ.ratio (p, j))) := by
  rw [socleExpectation, lintegral_gasMeasure_tsum θ
    (fun m => ENNReal.ofReal (Real.log ((m.1 : ℕ) : ℝ)))]
  have hcongr : (∑' m : AbelianZetaMode, ENNReal.ofReal (Real.log ((m.1 : ℕ) : ℝ))
        * ENNReal.ofReal (θ.ratio m / (1 - θ.ratio m)))
      = ∑' m : Nat.Primes × ℕ,
        (fun (p : Nat.Primes) (j : ℕ) => ENNReal.ofReal (Real.log ((p : ℕ) : ℝ))
          * ENNReal.ofReal (θ.ratio (p, j) / (1 - θ.ratio (p, j)))) m.1 m.2 :=
    tsum_congr fun m => rfl
  rw [hcongr]
  refine (ENNReal.tsum_prod (f := fun (p : Nat.Primes) (j : ℕ) =>
    ENNReal.ofReal (Real.log ((p : ℕ) : ℝ))
      * ENNReal.ofReal (θ.ratio (p, j) / (1 - θ.ratio (p, j))))).trans ?_
  refine tsum_congr fun p => ?_
  rw [← ENNReal.tsum_mul_left]

end AbelianZetaParameters

/-- At `τ = 0` the mode ratio at depth `j` is the `(j+1)`-st power of the prime nome, so the mode
mean is exactly `modeMean`. -/
theorem ratio_div_one_sub_eq_modeMean (σ : EulerSigma) (p : Nat.Primes) (j : ℕ) :
    (AbelianZetaParameters.temperatureParameters σ.val σ.pos).ratio (p, j)
        / (1 - (AbelianZetaParameters.temperatureParameters σ.val σ.pos).ratio (p, j))
      = modeMean (eqgQ σ (p : ℕ)) j := by
  have hratio : (AbelianZetaParameters.temperatureParameters σ.val σ.pos).ratio (p, j)
      = eqgQ σ (p : ℕ) ^ (j + 1) := by
    rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent, eqgQ_pow_succ]
    simp only [AbelianZetaParameters.temperatureParameters, AbelianZetaMode.depth]
    congr 1
    push_cast
    ring
  rw [hratio, modeMean]

/-- **(GAS.12), expectation side.**  At `τ = 0` the socle expectation is the prime-grouped sum of
the mode-mean ladders. -/
theorem socleExpectation_temperature (σ : EulerSigma) :
    AbelianZetaParameters.socleExpectation
        (AbelianZetaParameters.temperatureParameters σ.val σ.pos)
      = ∑' p : Nat.Primes, ENNReal.ofReal (Real.log ((p : ℕ) : ℝ))
        * ∑' j : ℕ, ENNReal.ofReal (modeMean (eqgQ σ (p : ℕ)) j) := by
  rw [AbelianZetaParameters.socleExpectation_eq]
  refine tsum_congr fun p => ?_
  congr 1
  exact tsum_congr fun j => by rw [ratio_div_one_sub_eq_modeMean σ p j]

namespace AbelianZetaParameters

end AbelianZetaParameters

/-! ## The canonical unit tilt -/

/-- The canonical unit tilt `P_{σ,σ}` of `ULF-EQG-1`. -/
def tiltParameters (σ : EulerSigma) : AbelianZetaParameters where
  sigma := σ.val
  tau := σ.val
  sigma_pos := σ.pos
  tau_nonneg := σ.pos.le

/-- Under the unit tilt the depth-`j` mode mean is the depth-`j+1` mean of the untilted gas. -/
theorem ratio_div_one_sub_eq_modeMean_tilt (σ : EulerSigma) (p : Nat.Primes) (j : ℕ) :
    (tiltParameters σ).ratio (p, j) / (1 - (tiltParameters σ).ratio (p, j))
      = modeMean (eqgQ σ (p : ℕ)) (j + 1) := by
  have hratio : (tiltParameters σ).ratio (p, j) = eqgQ σ (p : ℕ) ^ (j + 1 + 1) := by
    rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent, eqgQ_pow_succ]
    simp only [tiltParameters, AbelianZetaMode.depth]
    congr 1
    push_cast
    ring
  rw [hratio, modeMean]

/-- **(GAS.12), tilted expectation.**  The unit tilt shifts the mode-mean ladder by one depth. -/
theorem socleExpectation_tilt (σ : EulerSigma) :
    AbelianZetaParameters.socleExpectation (tiltParameters σ)
      = ∑' p : Nat.Primes, ENNReal.ofReal (Real.log ((p : ℕ) : ℝ))
        * ∑' j : ℕ, ENNReal.ofReal (modeMean (eqgQ σ (p : ℕ)) (j + 1)) := by
  rw [AbelianZetaParameters.socleExpectation_eq]
  refine tsum_congr fun p => ?_
  congr 1
  exact tsum_congr fun j => by rw [ratio_div_one_sub_eq_modeMean_tilt σ p j]

/-! ## (GAS.12) in additive form -/

theorem tsum_ofReal_modeMean_eq (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' j : ℕ, ENNReal.ofReal (modeMean q j))
      = ENNReal.ofReal (∑' j : ℕ, modeMean q j) :=
  (ENNReal.ofReal_tsum_of_nonneg (fun j => modeMean_nonneg hq0 hq1 j)
    (summable_modeMean hq0 hq1)).symm

theorem tsum_ofReal_modeMean_shift_eq (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' j : ℕ, ENNReal.ofReal (modeMean q (j + 1)))
      = ENNReal.ofReal (∑' j : ℕ, modeMean q (j + 1)) :=
  (ENNReal.ofReal_tsum_of_nonneg (fun j => modeMean_nonneg hq0 hq1 (j + 1))
    ((summable_nat_add_iff 1).mpr (summable_modeMean hq0 hq1))).symm

/-- **The mode-mean ladder splits off its depth-one term.** -/
theorem tsum_ofReal_modeMean_split (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' j : ℕ, ENNReal.ofReal (modeMean q j))
      = (∑' j : ℕ, ENNReal.ofReal (modeMean q (j + 1))) + ENNReal.ofReal (modeMean q 0) := by
  have hreal := (summable_modeMean hq0 hq1).tsum_eq_zero_add
  rw [tsum_ofReal_modeMean_eq q hq0 hq1, tsum_ofReal_modeMean_shift_eq q hq0 hq1, hreal,
    ENNReal.ofReal_add (modeMean_nonneg hq0 hq1 0)
      (tsum_nonneg fun j => modeMean_nonneg hq0 hq1 (j + 1)), add_comm]

/-- **(GAS.12), additive form.**  The socle expectation of the untilted gas is the socle expectation
of the canonical unit tilt plus the von Mangoldt mass — no subtraction and no finiteness hypothesis
is involved. -/
theorem socleExpectation_eq_tilt_add_residue (σ : EulerSigma) :
    AbelianZetaParameters.socleExpectation
        (AbelianZetaParameters.temperatureParameters σ.val σ.pos)
      = AbelianZetaParameters.socleExpectation (tiltParameters σ)
        + ∑' p : Nat.Primes, ENNReal.ofReal (Real.log ((p : ℕ) : ℝ))
          * ENNReal.ofReal (modeMean (eqgQ σ (p : ℕ)) 0) := by
  rw [socleExpectation_temperature σ, socleExpectation_tilt σ, ← ENNReal.tsum_add]
  refine tsum_congr fun p => ?_
  have hq0 : (0 : ℝ) ≤ eqgQ σ (p : ℕ) := (eqgQ_pos σ p.2.pos).le
  have hq1 : eqgQ σ (p : ℕ) < 1 := eqgQ_lt_one σ p.2.two_le
  rw [tsum_ofReal_modeMean_split (eqgQ σ (p : ℕ)) hq0 hq1, mul_add]

/-! ## The prime fibre -/

/-- The modes above a fixed prime. -/
def primeFiber (p : Nat.Primes) : Set AbelianZetaMode := {m : AbelianZetaMode | m.1 = p}

/-- Depths enumerate the modes above a fixed prime. -/
def primeFiberEquiv (p : Nat.Primes) : ℕ ≃ (primeFiber p) where
  toFun j := ⟨(p, j), rfl⟩
  invFun m := (m : AbelianZetaMode).2
  left_inv j := rfl
  right_inv m := by
    refine Subtype.ext ?_
    have hp : (m : AbelianZetaMode).1 = p := m.2
    exact Prod.ext hp.symm rfl

/-- **The prime fibre marginal of the gas is the product of its depth modes.**  This is the
factorisation the global form of (GAS.5) needs: the law of the socle exponent at `p` is determined
by the depth modes above `p` alone. -/
theorem gasMeasure_map_restrict_primeFiber (θ : AbelianZetaParameters) (p : Nat.Primes) :
    θ.gasMeasure.map (Set.restrict (primeFiber p))
      = MeasureTheory.Measure.infinitePi (fun i : primeFiber p => θ.modeLaw i) := by
  rw [AbelianZetaParameters.gasMeasure]
  exact MeasureTheory.Measure.infinitePi_map_restrict' (μ := θ.modeLaw)

/-- **The depth-indexed prime fibre marginal.**  Reading the fibre by depth, the marginal of the gas
above `p` is the product of the depth mode laws at `p`. -/
theorem gasMeasure_map_primeFiber_depths (θ : AbelianZetaParameters) (p : Nat.Primes) :
    θ.gasMeasure.map (fun k : AbelianZetaMode → ℕ => fun j : ℕ => k (p, j))
      = MeasureTheory.Measure.infinitePi (fun j : ℕ => θ.modeLaw (p, j)) := by
  classical
  set e := primeFiberEquiv p with he
  have hcongr := MeasureTheory.Measure.infinitePi_map_piCongrLeft
    (μ := fun i : primeFiber p => θ.modeLaw i) e
  have hfam : (fun j : ℕ => θ.modeLaw ((e j : AbelianZetaMode)))
      = fun j : ℕ => θ.modeLaw (p, j) := rfl
  rw [hfam] at hcongr
  have hmeasE : Measurable (MeasurableEquiv.piCongrLeft (fun _ : primeFiber p => ℕ) e) :=
    (MeasurableEquiv.piCongrLeft (fun _ : primeFiber p => ℕ) e).measurable
  have hback : (MeasureTheory.Measure.infinitePi (fun i : primeFiber p => θ.modeLaw i)).map
      (fun x : (primeFiber p) → ℕ => fun j : ℕ => x (e j))
      = MeasureTheory.Measure.infinitePi (fun j : ℕ => θ.modeLaw (p, j)) := by
    have hmeasBack : Measurable (fun x : (primeFiber p) → ℕ => fun j : ℕ => x (e j)) := by
      fun_prop
    rw [← hcongr, MeasureTheory.Measure.map_map hmeasBack hmeasE]
    have hid : ((fun x : (primeFiber p) → ℕ => fun j : ℕ => x (e j))
        ∘ (MeasurableEquiv.piCongrLeft (fun _ : primeFiber p => ℕ) e)) = id := by
      funext y j
      show (MeasurableEquiv.piCongrLeft (fun _ : primeFiber p => ℕ) e) y (e j) = y j
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rw [hid, MeasureTheory.Measure.map_id]
  have hsplit : (fun k : AbelianZetaMode → ℕ => fun j : ℕ => k (p, j))
      = (fun x : (primeFiber p) → ℕ => fun j : ℕ => x (e j)) ∘ Set.restrict (primeFiber p) := rfl
  rw [hsplit, ← MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop),
    gasMeasure_map_restrict_primeFiber θ p, hback]

/-- **The atom mass of a depth configuration at a prime.**  Under the depth product at `p` a single
configuration has the product of its mode masses. -/
theorem infinitePi_depthModes_singleton (θ : AbelianZetaParameters) (p : Nat.Primes)
    (g : ℕ → ℕ) :
    MeasureTheory.Measure.infinitePi (fun j : ℕ => θ.modeLaw (p, j)) {g}
      = ∏' j : ℕ, θ.modeLaw (p, j) {g j} :=
  MeasureTheory.Measure.infinitePi_singleton (μ := fun j : ℕ => θ.modeLaw (p, j)) g

/-- The atom mass in the mode-ratio form the Euler weight is summed from. -/
theorem infinitePi_depthModes_singleton_ratio (θ : AbelianZetaParameters) (p : Nat.Primes)
    (g : ℕ → ℕ) :
    MeasureTheory.Measure.infinitePi (fun j : ℕ => θ.modeLaw (p, j)) {g}
      = ∏' j : ℕ, ENNReal.ofReal
        ((θ.ratio (p, j)) ^ (g j) * (1 - θ.ratio (p, j))) := by
  rw [infinitePi_depthModes_singleton θ p g]
  exact tprod_congr fun j => θ.modeLaw_singleton (p, j) (g j)

/-! ## Transporting a real product to `ℝ≥0∞` -/

/-- **A convergent product of nonnegative reals transports to `ℝ≥0∞`.**  The route is the corpus's
own device: pass through `ℝ≥0` by the closed embedding into `ℝ`, then push forward to `ℝ≥0∞`. -/
theorem hasProd_ofReal {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) {L : ℝ}
    (hL : HasProd f L) : HasProd (fun i => ENNReal.ofReal (f i)) (ENNReal.ofReal L) := by
  have hLnn : 0 ≤ L := by
    refine ge_of_tendsto hL ?_
    filter_upwards with s
    exact Finset.prod_nonneg fun i _ => hf i
  have hcoe : ∀ i, (((f i).toNNReal : ℝ≥0) : ℝ) = f i := fun i => Real.coe_toNNReal (f i) (hf i)
  have hcoeL : ((L.toNNReal : ℝ≥0) : ℝ) = L := Real.coe_toNNReal L hLnn
  have hreal : HasProd (fun i => (((f i).toNNReal : ℝ≥0) : ℝ)) ((L.toNNReal : ℝ≥0) : ℝ) := by
    have hfun : (fun i => (((f i).toNNReal : ℝ≥0) : ℝ)) = f := funext hcoe
    rw [hfun, hcoeL]
    exact hL
  have hnn : HasProd (fun i => (f i).toNNReal) L.toNNReal :=
    (NNReal.isClosedEmbedding_coe.isInducing.hasProd_iff
      (g := NNReal.toRealHom.toMonoidHom) (fun i => (f i).toNNReal) L.toNNReal).mp hreal
  have henn := hnn.map (ENNReal.ofNNRealHom : ℝ≥0 →+* ℝ≥0∞).toMonoidHom ENNReal.continuous_coe
  simp only [Function.comp_def] at henn
  exact henn

theorem tprod_ofReal {ι : Type*} {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) {L : ℝ}
    (hL : HasProd f L) : (∏' i : ι, ENNReal.ofReal (f i)) = ENNReal.ofReal L :=
  (hasProd_ofReal hf hL).tprod_eq

/-! ## The exact-parts event -/

/-- The event that the depth configuration above `p` has exactly `n` cyclic factors. -/
def exactPartsEvent (n : ℕ) : Set (ℕ → ℕ) :=
  ⋃ g : {g : PartConfig // partCount g = n}, {((g.1 : ℕ →₀ ℕ) : ℕ → ℕ)}

/-- **The exact-parts event is the disjoint union of its configuration atoms.** -/
theorem measure_exactPartsEvent (θ : AbelianZetaParameters) (p : Nat.Primes) (n : ℕ) :
    MeasureTheory.Measure.infinitePi (fun j : ℕ => θ.modeLaw (p, j)) (exactPartsEvent n)
      = ∑' g : {g : PartConfig // partCount g = n},
        MeasureTheory.Measure.infinitePi (fun j : ℕ => θ.modeLaw (p, j))
          {((g.1 : ℕ →₀ ℕ) : ℕ → ℕ)} := by
  classical
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun g : {g : PartConfig // partCount g = n} => ({((g.1 : ℕ →₀ ℕ) : ℕ → ℕ)} : Set (ℕ → ℕ)))) := by
    intro g h hne
    refine Set.disjoint_singleton.mpr ?_
    intro hcoe
    exact hne (Subtype.ext (DFunLike.coe_injective hcoe))
  rw [exactPartsEvent, MeasureTheory.measure_iUnion hdisj
    (fun _ => MeasurableSet.singleton _)]

/-- **(GAS.5), global form at a prime.**  The mass of the exact-parts event is the local socle mass,
hence the Euler weight. -/
theorem measure_exactPartsEvent_eq_localSocleMass (σ : EulerSigma) (p : Nat.Primes) (n : ℕ) :
    MeasureTheory.Measure.infinitePi
        (fun j : ℕ => (AbelianZetaParameters.temperatureParameters σ.val σ.pos).modeLaw (p, j))
        (exactPartsEvent n)
      = localSocleMass (eqgNome σ p) n := by
  classical
  rw [measure_exactPartsEvent, ← tsum_localModeMass_eq_localSocleMass (eqgNome σ p) n]
  refine tsum_congr fun g => ?_
  rw [infinitePi_depthModes_singleton_ratio]
  have hratio : ∀ j : ℕ,
      (AbelianZetaParameters.temperatureParameters σ.val σ.pos).ratio (p, j)
        = (eqgNome σ p).val ^ (j + 1) := by
    intro j
    rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent, eqgNome_val, eqgQ_pow_succ]
    simp only [AbelianZetaParameters.temperatureParameters, AbelianZetaMode.depth]
    congr 1
    push_cast
    ring
  have hfun : (fun j : ℕ => ENNReal.ofReal
        (((AbelianZetaParameters.temperatureParameters σ.val σ.pos).ratio (p, j)) ^ (g.1 j)
          * (1 - (AbelianZetaParameters.temperatureParameters σ.val σ.pos).ratio (p, j))))
      = fun j : ℕ => ENNReal.ofReal
        (((eqgNome σ p).val ^ (j + 1)) ^ (g.1 j) * (1 - (eqgNome σ p).val ^ (j + 1))) := by
    funext j
    rw [hratio j]
  rw [hfun]
  refine tprod_ofReal (fun j => ?_) ?_
  · have h1 : (0 : ℝ) ≤ ((eqgNome σ p).val ^ (j + 1)) ^ (g.1 j) :=
      pow_nonneg (pow_nonneg (eqgNome σ p).pos.le _) _
    have h2 : (0 : ℝ) ≤ 1 - (eqgNome σ p).val ^ (j + 1) :=
      (one_sub_pow_pos (eqgNome σ p).pos.le (eqgNome σ p).lt_one j).le
    exact mul_nonneg h1 h2
  · exact ((multipliable_occupation_pow (eqgNome σ p) g.1).mul
      (realQFactorial_multipliable (eqgNome σ p))).hasProd

/-- **(GAS.5).**  Under the abelian zeta gas at temperature `σ`, the socle exponent at `p` has the
Euler law of `ULF-EQG-1`: the probability of exactly `n` cyclic factors at `p` is
`(q;q)_∞ · w` with `w` the random-integer weight at `pⁿ`. -/
theorem gas_socle_law (σ : EulerSigma) (p : Nat.Primes) (n : ℕ) :
    (MeasureTheory.Measure.infinitePi
        (fun j : ℕ => (AbelianZetaParameters.temperatureParameters σ.val σ.pos).modeLaw (p, j))
        (exactPartsEvent n)).toReal
      = realQFactorialInf (eqgNome σ p) * eqgWeight σ ((p : ℕ) ^ n) := by
  rw [measure_exactPartsEvent_eq_localSocleMass σ p n, localSocleMass_toReal,
    eqgWeight_prime_pow σ p n]

/-! ## The density constant of the canonical tilt -/

/-- The untilted gas at temperature `σ > 1`, in the convergence chamber. -/
def temperatureConv (σ : EulerSigma) : AbelianZetaConvergentParameters where
  toAbelianZetaParameters := AbelianZetaParameters.temperatureParameters σ.val σ.pos
  firstDepth := by
    have := σ.one_lt
    simpa [AbelianZetaParameters.temperatureParameters] using this

@[simp] theorem temperatureConv_sigma (σ : EulerSigma) : (temperatureConv σ).sigma = σ.val := rfl

@[simp] theorem temperatureConv_tau (σ : EulerSigma) : (temperatureConv σ).tau = 0 := rfl

/-- **The density constant of the canonical tilt is `ζ(σ)`.**  This is (GAS.7) at `τ = 0`: the
partition function of the untilted gas is `ζ(σ)` times that of the unit tilt, so the
Radon–Nikodym density of `P_{σ,σ}` against `P_σ` is `ζ(σ)·|soc A|^{−σ}`. -/
theorem zetaPartition_temperatureConv (σ : EulerSigma) :
    (temperatureConv σ).zetaPartition
      = riemannZeta (((σ.val : ℝ) : ℂ)) * (temperatureConv σ).depthShift.zetaPartition := by
  have h := zetaPartition_depthShift (temperatureConv σ)
  have harg : ((temperatureConv σ).sigma + (temperatureConv σ).tau : ℝ) = σ.val := by
    simp
  rw [harg] at h
  exact h

/-! ## The atomwise density of the canonical tilt -/

/-- **The unit tilt multiplies the Gibbs weight by `|soc A|^{−σ}`.**  Together with
`zetaPartition_temperatureConv` this is the Radon–Nikodym density `ζ(σ)·|soc A|^{−σ}` of the card. -/
theorem twoObservableWeight_tiltParameters (σ : EulerSigma) (A : AbelianZetaGroupClass) :
    abelianZetaTwoObservableWeight (tiltParameters σ) A
      = abelianZetaTwoObservableWeight
          (AbelianZetaParameters.temperatureParameters σ.val σ.pos) A
        * ((A.socleOrder : ℝ) ^ (-σ.val)) := by
  show ((A.order : ℝ) ^ (-σ.val) * (A.socleOrder : ℝ) ^ (-σ.val))
      = ((A.order : ℝ) ^ (-σ.val) * (A.socleOrder : ℝ) ^ (-(0 : ℝ)))
        * (A.socleOrder : ℝ) ^ (-σ.val)
  rw [neg_zero, Real.rpow_zero, mul_one]


end

end GaloisForLFunctions.HTGeometry
