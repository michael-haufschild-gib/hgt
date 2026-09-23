import GaloisForLFunctions.RHTower.SelbergMaassSliceRigidity

/-!
# The complete closed-period resistance/current product

The full augmented unit source closes after the level period `N+1`.
For two points strictly inside that period, the original weighted chord
inequality applies to both complementary arcs. Exact resistance and
current splitting give four times the squared chord as a lower bound for
the complete period product. The scalar integrands have unit period, so
this is `(N+1)^(2 : ℕ)` times the original unit-period product.

For a nonzero cuspidal source with eigenvalue strictly between zero and
one quarter, every positive height has positive integrated source mass.
The original zero means therefore supply negative correlation on each
height. Its augmented chord has a fixed margin above two for all small
positive regulators. Consequently the level-scaled product has a fixed
margin above eight, including at common-zero heights.

Every finite product limit satisfies the same strict lower threshold.
When the current factor tends to zero, its product with the reciprocal
amplitude integral still cannot vanish. This gives an inverse-resistance
lower rate for the complete current, without assuming a finite product
limit or a nodal order. It does not exclude common flat nodes or prove
positive limiting current at every height.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory ModularGroup
open scoped BigOperators ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassClosedPeriodProduct
noncomputable section

/-- Two positive-resistance arcs carrying the same chord obey the exact effective-resistance comparison. -/
theorem two_arc_effective_resistance {d r₁ r₂ e₁ e₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁ : d ≤ r₁*e₁) (h₂ : d ≤ r₂*e₂) :
    d*(r₁+r₂) ≤ r₁*r₂*(e₁+e₂) := by
  have hA := mul_le_mul_of_nonneg_left h₁ hr₂.le
  have hB := mul_le_mul_of_nonneg_left h₂ hr₁.le
  nlinarith

/-- A closed two-arc path charges its common squared chord four times to the total product. -/
theorem two_arc_product_lower {d r₁ r₂ e₁ e₂ : ℝ} (hd : 0 ≤ d)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (h₁ : d ≤ r₁*e₁) (h₂ : d ≤ r₂*e₂) :
    4*d ≤ (r₁+r₂)*(e₁+e₂) := by
  have h := two_arc_effective_resistance hr₁ hr₂ h₁ h₂
  have hh := mul_le_mul_of_nonneg_left h (add_pos hr₁ hr₂).le
  have hdiff := mul_nonneg hd (sq_nonneg (r₁-r₂))
  have hr := mul_pos hr₁ hr₂
  nlinarith

open SelbergMaassCongruenceTrace SelbergMaassMean SelbergMaassTraceEnergy
open SelbergMaassSourceCurrents SelbergMaassTraceRegularized SelbergMaassRegulatorMass
open SelbergMaassChordEnergy SelbergMaassUnipotentPaths SelbergMaassTraceDirection
open SelbergMaassAugmentedDirection SelbergMaassSliceRigidity
open SelbergMaassPeriodResistance SelbergMaassPeriodCurrentLimit
variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Every coordinate of the full augmented source closes after the actual level period. -/
theorem source_level_periodic (e : Ioi (0:ℝ)) (j : Option (Deck N)) {y : ℝ}
    (hy : 0 < y) (x : ℝ) :
    source N f e j (point (x+(N+1:ℕ)) y)=source N f e j (point x y) := by
  cases j with
  | none => rfl
  | some q => exact maass_periodic N (quotientForm N f q) x hy

/-- The actual regulated radius has the same complete level period. -/
theorem radius_level_periodic (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    radius N f e (point (x+(N+1:ℕ)) y)=radius N f e (point x y) := by
  have h : radius N f e (point (x+(N+1:ℕ)) y)^(2 : ℕ)=radius N f e (point x y)^(2 : ℕ) := by
    rw [← source_normSq,← source_normSq]
    apply Finset.sum_congr rfl
    intro j _
    rw [source_level_periodic N f e j hy x]
  nlinarith [radius_pos N f e (point (x+(N+1:ℕ)) y),radius_pos N f e (point x y)]

/-- Every actual augmented unit coordinate closes, including at original common zeros. -/
theorem unit_level_periodic (e : Ioi (0:ℝ)) (j : Option (Deck N)) {y : ℝ}
    (hy : 0 < y) (x : ℝ) :
    unit N f e j (point (x+(N+1:ℕ)) y)=unit N f e j (point x y) := by
  unfold SelbergMaassAugmentedDirection.unit
  rw [source_level_periodic N f e j hy x,radius_level_periodic N f e hy x]

/-- The second arc of the actual closed level-period loop has the same endpoint chord. -/
theorem closed_arc_distance (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    distanceSq N f e (ofComplex (point b y)) (ofComplex (point (a+(N+1:ℕ)) y))=
      distanceSq N f e (ofComplex (point a y)) (ofComplex (point b y)) := by
  unfold distanceSq
  simp only [coe_ofComplex_point _ hy,unit_level_periodic N f e _ hy a]
  apply Finset.sum_congr rfl
  intro j _
  simp only [normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

/-- Resistance splits exactly across an arbitrary intermediate point of a source height. -/
theorem pathResistance_add (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) (a b c : ℝ) :
    pathResistance N f e y a b+pathResistance N f e y b c=pathResistance N f e y a c := by
  exact intervalIntegral.integral_add_adjacent_intervals
    ((continuous_const.div (radius_slice_continuous N f e hy)
      (fun x => (radius_pos N f e (point x y)).ne')).intervalIntegrable a b)
    ((continuous_const.div (radius_slice_continuous N f e hy)
      (fun x => (radius_pos N f e (point x y)).ne')).intervalIntegrable b c)

/-- Full retained current energy has the same exact splitting. -/
theorem pathEnergy_add (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) (a b c : ℝ) :
    pathEnergy N f e y a b+pathEnergy N f e y b c=pathEnergy N f e y a c :=
  intervalIntegral.integral_add_adjacent_intervals (path_energy_intervalIntegrable N f e hy a b)
    (path_energy_intervalIntegrable N f e hy b c)

/-- The complete level-period product is exactly level-width squared times the original unit-period product. -/
theorem level_period_product (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y) (a : ℝ) :
    pathResistance N f e y a (a+(N+1:ℕ))*pathEnergy N f e y a (a+(N+1:ℕ))=
      ((N+1:ℕ):ℝ)^(2 : ℕ)*periodCost N f e y := by
  have hr := pathResistance_integer N f e hy a ((N+1:ℕ):ℤ)
  have he := pathEnergy_integer N f e hy a ((N+1:ℕ):ℤ)
  simp only [Int.cast_natCast,pathResistance_one_period N f e hy,pathEnergy_one_period N f e hy] at hr he
  rw [hr,he]
  unfold periodCost
  ring

/-- Both arcs of the actual source loop give a uniform full-period chord comparison. -/
theorem four_chord_le_level_product (e : Ioi (0:ℝ)) {y : ℝ} (hy : 0 < y)
    {a b : ℝ} (hab : a < b) (hba : b < a+(N+1:ℕ)) :
    4*distanceSq N f e (ofComplex (point a y)) (ofComplex (point b y)) ≤
      ((N+1:ℕ):ℝ)^(2 : ℕ)*periodCost N f e y := by
  have h₁ := chord_le_resistance_energy N f e hy hab.le
  have h₂ := chord_le_resistance_energy N f e hy hba.le
  rw [closed_arc_distance N f e hy a b] at h₂
  have h := two_arc_product_lower
    (show 0 ≤ distanceSq N f e (ofComplex (point a y)) (ofComplex (point b y)) from
      Finset.sum_nonneg (fun _ _ => normSq_nonneg _))
    (pathResistance_pos N f e hy hab) (pathResistance_pos N f e hy hba) h₁ h₂
  rw [pathResistance_add N f e hy,pathEnergy_add N f e hy,level_period_product N f e hy] at h
  exact h

/-- The complete augmented chord is symmetric in its actual source endpoints. -/
theorem augmented_distance_symm (e : Ioi (0:ℝ)) (z w : ℍ) :
    distanceSq N f e z w=distanceSq N f e w z := by
  unfold distanceSq
  apply Finset.sum_congr rfl
  intro j _
  simp only [normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

/-- Original regulated radii increase with the positive regulator. -/
theorem radius_mono_regulator {e r : Ioi (0:ℝ)} (he : (e:ℝ) ≤ (r:ℝ)) (z : ℂ) :
    radius N f e z ≤ radius N f r z := by
  apply Real.sqrt_le_sqrt
  have hh := mul_nonneg (sub_nonneg.mpr he) (add_nonneg r.2.le e.2.le)
  change density N f (ofComplex z)+(e:ℝ)^(2 : ℕ) ≤ density N f (ofComplex z)+(r:ℝ)^(2 : ℕ)
  nlinarith

/-- A negative original correlation gives a fixed augmented chord margin above two at every small regulator. -/
theorem uniform_chord_margin_of_negative_correlation (z w : ℍ)
    (hc : correlation N f z w < 0) :
    ∃ r : Ioi (0:ℝ), ∃ d : ℝ, 2 < d ∧
      ∀ e : Ioi (0:ℝ), (e:ℝ) ≤ (r:ℝ) → d ≤ distanceSq N f e z w := by
  let oneE : Ioi (0:ℝ) := ⟨1,by norm_num⟩
  let Q : ℝ := radius N f oneE (z:ℂ)*radius N f oneE (w:ℂ)
  have hQ : 0 < Q := mul_pos (radius_pos N f oneE _) (radius_pos N f oneE _)
  let δ : ℝ := -correlation N f z w/Q
  have hδ : 0 < δ := div_pos (by linarith) hQ
  have hδQ : δ*Q = -correlation N f z w := by dsimp [δ]; field_simp
  have hs : 0 < Real.sqrt (-correlation N f z w)/2 :=
    div_pos (Real.sqrt_pos.mpr (by linarith)) (by norm_num)
  let r : Ioi (0:ℝ) := ⟨min 1 (Real.sqrt (-correlation N f z w)/2),lt_min (by norm_num) hs⟩
  refine ⟨r,2+δ,by linarith,?_⟩
  intro e he
  have he1 : (e:ℝ) ≤ (oneE:ℝ) := he.trans (min_le_left _ _)
  have heS : (e:ℝ) ≤ Real.sqrt (-correlation N f z w)/2 := he.trans (min_le_right _ _)
  have hsq : (e:ℝ)^(2 : ℕ) ≤ -correlation N f z w/4 := by
    have h := mul_nonneg (sub_nonneg.mpr heS) (add_nonneg hs.le e.2.le)
    have hh := Real.sq_sqrt (show 0 ≤ -correlation N f z w by linarith)
    nlinarith
  have hR : radius N f e (z:ℂ)*radius N f e (w:ℂ) ≤ Q :=
    mul_le_mul (radius_mono_regulator N f he1 _) (radius_mono_regulator N f he1 _)
      (radius_pos N f e _).le (radius_pos N f oneE _).le
  have hδR := mul_le_mul_of_nonneg_left hR hδ.le
  have hcor := correlation_eq_radii_mul N f e z w
  have hp := mul_pos (radius_pos N f e (z:ℂ)) (radius_pos N f e (w:ℂ))
  have hdu : δ ≤ -2*unitCorrelation N f e z w := by
    apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith
  rw [distanceSq_eq]
  linarith

variable (mu : Ioo (0:ℝ) (1/4))
    (g : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) (mu:ℝ))

/-- Every actual positive height supplies a fixed separated pair strictly inside one closed level period. -/
theorem source_closed_period_margin {y : ℝ} (hy : 0 < y) :
    ∃ a b : ℝ, a < b ∧ b < a+(N+1:ℕ) ∧
      ∃ r : Ioi (0:ℝ), ∃ d : ℝ, 2 < d ∧
        ∀ e : Ioi (0:ℝ), (e:ℝ) ≤ (r:ℝ) →
          d ≤ distanceSq N g e (ofComplex (point a y)) (ofComplex (point b y)) := by
  obtain ⟨x,_hx,hD⟩ := exceptional_density_pos_in_unit_period N mu g hy
  let z : ℍ := ofComplex (point x y)
  have him : z.im=y := by
    change ((ofComplex (point x y):ℍ):ℂ).im=y
    rw [coe_ofComplex_point x hy]
    simp [point]
  have hre : z.re=x := by
    change ((ofComplex (point x y):ℍ):ℂ).re=x
    rw [coe_ofComplex_point x hy]
    simp [point]
  obtain ⟨t,ht,hc⟩ := exists_negative_correlation N mu g z hD
  rw [him] at hc
  rw [hre] at ht
  obtain ⟨r,d,hd,hsep⟩ := uniform_chord_margin_of_negative_correlation N g z (ofComplex (point t y)) hc
  have hne : x ≠ t := by
    intro h
    subst t
    change correlation N g z z < 0 at hc
    rw [correlation_self] at hc
    exact (not_lt_of_ge hD.le) hc
  have hw : (0:ℝ) < (N+1:ℕ) := by positivity
  rcases lt_or_gt_of_ne hne with hxt | htx
  · refine ⟨x,t,hxt,by linarith [ht.2],r,d,hd,?_⟩
    exact hsep
  · refine ⟨t,x,htx,by linarith [ht.1],r,d,hd,?_⟩
    intro e he
    rw [augmented_distance_symm]
    exact hsep e he

/-- Complete original resistance/current products have a strict level-scaled floor at every height, including nodal heights. -/
theorem source_period_product_floor {y : ℝ} (hy : 0 < y) :
    ∃ r : Ioi (0:ℝ), ∃ c : ℝ, 8 < c ∧
      ∀ e : Ioi (0:ℝ), (e:ℝ) ≤ (r:ℝ) → c ≤ ((N+1:ℕ):ℝ)^(2 : ℕ)*periodCost N g e y := by
  obtain ⟨a,b,hab,hba,r,d,hd,hsep⟩ := source_closed_period_margin N mu g hy
  refine ⟨r,4*d,by linarith,?_⟩
  intro e he
  exact (mul_le_mul_of_nonneg_left (hsep e he) (by norm_num : (0:ℝ)≤4)).trans
    (four_chord_le_level_product N g e hy hab hba)

/-- A fixed positive product floor survives uniformly over all sufficiently small regulators. -/
theorem eventually_source_period_product_floor {y : ℝ} (hy : 0 < y) :
    ∃ c : ℝ, 8 < c ∧ ∀ᶠ e : Ioi (0:ℝ) in regulatorAtZero,
      c ≤ ((N+1:ℕ):ℝ)^(2 : ℕ)*periodCost N g e y := by
  obtain ⟨r,c,hc,h⟩ := source_period_product_floor N mu g hy
  refine ⟨c,hc,?_⟩
  have he := (tendsto_order.mp regulator_coe_limit).2 (r:ℝ) r.2
  exact he.mono (fun e he => h e he.le)

/-- The complete current cannot decay faster than a fixed inverse-resistance scale. -/
theorem eventually_current_gt_inverse_resistance {y : ℝ} (hy : 0 < y) :
    ∀ᶠ e : Ioi (0:ℝ) in regulatorAtZero,
      8 / (((N+1:ℕ):ℝ)^(2 : ℕ) * periodResistance N g e y) < periodCurrentEnergy N g e y := by
  obtain ⟨c,hc,h⟩ := eventually_source_period_product_floor N mu g hy
  filter_upwards [h] with e he
  have hR : 0 < periodResistance N g e y := pathResistance_pos N g e hy (by norm_num)
  have hw : 0 < ((N+1:ℕ):ℝ)^(2 : ℕ) := by positivity
  apply (div_lt_iff₀ (mul_pos hw hR)).mpr
  have hh := hc.trans_le he
  unfold periodCost at hh
  nlinarith

/-- Any finite limit of an actual period product lies strictly above its level-scaled threshold. -/
theorem finite_product_limit_strict_lower {y L : ℝ} (hy : 0 < y)
    (hL : Tendsto (fun e : Ioi (0:ℝ) => periodCost N g e y) regulatorAtZero (𝓝 L)) :
    8 < ((N+1:ℕ):ℝ)^(2 : ℕ)*L := by
  obtain ⟨c,hc,h⟩ := eventually_source_period_product_floor N mu g hy
  exact hc.trans_le (ge_of_tendsto (tendsto_const_nhds.mul hL) h)

/-- The full source product never tends to zero, even if its current factor does. -/
theorem period_product_not_tendsto_zero {y : ℝ} (hy : 0 < y) :
    ¬ Tendsto (fun e : Ioi (0:ℝ) => periodCost N g e y) regulatorAtZero (𝓝 0) := by
  intro h
  have hh := finite_product_limit_strict_lower N mu g hy h
  norm_num at hh

/-- On zero-free original periods, the exact unregularized product satisfies the same strict source threshold. -/
theorem zero_free_limiting_product_strict_lower {y : ℝ} (hy : 0 < y)
    (hp : ∀ x ∈ Icc (0:ℝ) 1, 0 < density N g (ofComplex (point x y))) :
    8 < ((N+1:ℕ):ℝ)^(2 : ℕ) *
      (unregularizedPeriodResistance N g y * periodCurrentLimit N g y) :=
  finite_product_limit_strict_lower N mu g hy (periodCost_tendsto_of_zero_free N g hy hp)

/-- A vanishing limiting current still retains a positive complete period-product floor and an inverse-resistance current bound. -/
theorem zero_current_retains_product_floor {y : ℝ} (hy : 0 < y)
    (hE : periodCurrentLimit N g y=0) :
    Tendsto (fun e : Ioi (0:ℝ) => periodCurrentEnergy N g e y) regulatorAtZero (𝓝 0) ∧
      (∃ c : ℝ, 8 < c ∧ ∀ᶠ e : Ioi (0:ℝ) in regulatorAtZero,
        c ≤ ((N+1:ℕ):ℝ)^(2 : ℕ) * periodCost N g e y) ∧
      (∀ᶠ e : Ioi (0:ℝ) in regulatorAtZero,
        8 / (((N+1:ℕ):ℝ)^(2 : ℕ) * periodResistance N g e y) < periodCurrentEnergy N g e y) := by
  refine ⟨?_,eventually_source_period_product_floor N mu g hy,
    eventually_current_gt_inverse_resistance N mu g hy⟩
  simpa only [hE] using periodCurrentEnergy_tendsto N g hy

end
end GaloisForLFunctions.RHTower.SelbergMaassClosedPeriodProduct
