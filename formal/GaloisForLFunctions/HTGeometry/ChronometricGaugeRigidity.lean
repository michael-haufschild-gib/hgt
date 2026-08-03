import GaloisForLFunctions.HTGeometry.ChronometricRigiditySharpness

/-!
# Chronometric rigidity with extra gravitational sectors and gauge freedom

The branch-safe rigidity theorem is stated for a gauge-fixed law on metric fields alone. Extra
gravitational fields break its hypothesis: the clock encoding cannot be injective on a geometry
that carries a sector it does not resolve.

The correct replacement is not injectivity but *fibre constancy*: a law that is a function of the
observation is determined by the branch-safe graph, whether or not the encoding separates points.
This is strictly weaker than injectivity and is exactly what a gauge-invariant law satisfies once
its extra sector is reported completely up to gauge.

Concretely: if the clock encoding is injective on the metric sector and the reporter determines the
extra sector up to a field redefinition, then any two gauge-invariant laws with equal branch-safe
graphs are equal. If instead the extra sector is unreported, the clock-dark no-go applies and
rigidity fails.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-! ## Fibre-constant laws -/

section FiberConstant

variable {Geometry : Type u} {Source : Type v} {Observation : Type w}

/-- A law is a function of the observation. -/
def FiberConstant (encode : Geometry → Observation) (law : Geometry → Source) : Prop :=
  ∀ a b, encode a = encode b → law a = law b

/-- **Branch-safe rigidity for laws that are functions of the observation.**

This replaces injectivity of the encoding by the weaker requirement that the laws themselves do not
separate observationally identical geometries. Fibre constancy of either law is enough; both are
recorded because both hold in the intended application. -/
theorem chronometricSolutionGraph_eq_iff_of_fiberConstant
    {encode : Geometry → Observation} {law₁ law₂ : Geometry → Source}
    (_h₁ : FiberConstant encode law₁) (h₂ : FiberConstant encode law₂) :
    chronometricSolutionGraph encode law₁ = chronometricSolutionGraph encode law₂ ↔
      law₁ = law₂ := by
  constructor
  · intro hgraph
    funext g
    have hmem : (law₁ g, encode g) ∈ chronometricSolutionGraph encode law₂ := by
      rw [← hgraph]
      exact ⟨g, rfl⟩
    obtain ⟨g', hg'⟩ := hmem
    have hsource : law₂ g' = law₁ g := congrArg Prod.fst hg'
    have hobs : encode g' = encode g := congrArg Prod.snd hg'
    rw [← hsource, h₂ g' g hobs]
  · intro hlaw
    rw [hlaw]

/-- Every law is fibre constant for an injective encoding, so the injective rigidity theorem is the
special case of the fibre-constant one. -/
theorem fiberConstant_of_injective {encode : Geometry → Observation}
    (hinj : Function.Injective encode) (law : Geometry → Source) :
    FiberConstant encode law := by
  intro a b hab
  rw [hinj hab]

end FiberConstant

/-! ## Extra gravitational sectors reported up to gauge -/

section Gauge

variable {Metric : Type u} {Extra : Type u} {MetricObs : Type w} {Report : Type w}
  {Source : Type v} {Gauge : Type*}

/-- Reporter-complete chronometric observation of a geometry with an extra gravitational sector:
the clock encoding of the metric together with the reporter channel of the extra field. -/
def reporterCompleteEncode (enc : Metric → MetricObs) (rep : Extra → Report) :
    Metric × Extra → MetricObs × Report :=
  fun p => (enc p.1, rep p.2)

/-- A law is gauge invariant when a field redefinition of the extra sector does not change it. -/
def GaugeInvariant (act : Gauge → Extra → Extra) (law : Metric × Extra → Source) : Prop :=
  ∀ (γ : Gauge) (g : Metric) (e : Extra), law (g, act γ e) = law (g, e)

/-- A reporter is complete for a gauge action when equal reports mean equal fields up to a field
redefinition. -/
def ReporterComplete (rep : Extra → Report) (act : Gauge → Extra → Extra) : Prop :=
  ∀ e₁ e₂, rep e₁ = rep e₂ → ∃ γ : Gauge, e₂ = act γ e₁

/-- A gauge-invariant law with a complete reporter is a function of the reporter-complete
observation. -/
theorem fiberConstant_of_gaugeInvariant
    {enc : Metric → MetricObs} (hinj : Function.Injective enc)
    {rep : Extra → Report} {act : Gauge → Extra → Extra}
    (hcomplete : ReporterComplete rep act)
    {law : Metric × Extra → Source} (hgauge : GaugeInvariant act law) :
    FiberConstant (reporterCompleteEncode enc rep) law := by
  rintro ⟨g₁, e₁⟩ ⟨g₂, e₂⟩ hobs
  have hmetric : enc g₁ = enc g₂ := congrArg Prod.fst hobs
  have hreport : rep e₁ = rep e₂ := congrArg Prod.snd hobs
  obtain ⟨γ, hγ⟩ := hcomplete e₁ e₂ hreport
  rw [hinj hmetric] at *
  rw [hγ, hgauge γ g₂ e₁]

/-- **Chronometric rigidity with an extra gravitational sector.**

If the clock encoding is injective on the metric sector and the reporter determines the extra
sector up to a field redefinition, then two gauge-invariant nonlinear laws have identical
branch-safe solution graphs exactly when they are the same operator. Injectivity of the complete
encoding is not required and generally fails. -/
theorem chronometricGaugeRigidity
    {enc : Metric → MetricObs} (hinj : Function.Injective enc)
    {rep : Extra → Report} {act : Gauge → Extra → Extra}
    (hcomplete : ReporterComplete rep act)
    {law₁ law₂ : Metric × Extra → Source}
    (hg₁ : GaugeInvariant act law₁) (hg₂ : GaugeInvariant act law₂) :
    chronometricSolutionGraph (reporterCompleteEncode enc rep) law₁ =
        chronometricSolutionGraph (reporterCompleteEncode enc rep) law₂ ↔
      law₁ = law₂ :=
  chronometricSolutionGraph_eq_iff_of_fiberConstant
    (fiberConstant_of_gaugeInvariant hinj hcomplete hg₁)
    (fiberConstant_of_gaugeInvariant hinj hcomplete hg₂)

end Gauge

/-! ## A scalar gravitational potential, reported by its differences -/

section Potential

variable {Event : Type u}

/-- A scalar gravitational potential is physical only up to an additive constant. Its reporter
channel is the field of potential differences. -/
def potentialReporter (phi : Event → ℝ) : Event → Event → ℝ :=
  fun x y => phi x - phi y

/-- Adding a constant does not change any potential difference. -/
theorem potentialReporter_gaugeInvariant (c : ℝ) (phi : Event → ℝ) :
    potentialReporter (fun x => c + phi x) = potentialReporter phi := by
  funext x y
  simp only [potentialReporter]
  ring

/-- **The difference channel is reporter complete.** Equal potential differences mean the two
potentials differ by a constant field redefinition. -/
theorem potentialReporter_complete [Nonempty Event] :
    ReporterComplete (potentialReporter (Event := Event)) (fun c phi => fun x => c + phi x) := by
  intro phi psi hrep
  obtain ⟨x₀⟩ := ‹Nonempty Event›
  refine ⟨psi x₀ - phi x₀, ?_⟩
  funext x
  have hx := congrFun (congrFun hrep x) x₀
  simp only [potentialReporter] at hx
  linarith

/-- **Chronometric rigidity with a scalar gravitational potential.**

The clock channel resolves the metric, the difference channel resolves the potential up to its
additive gauge, and gauge-invariant nonlinear laws are then determined by their branch-safe
solution graphs. -/
theorem chronometricGaugeRigidity_potential
    {Tangent : Type u} [AddCommGroup Tangent] [Module ℝ Tangent] [Nonempty Event]
    {Source : Type v}
    {law₁ law₂ : ChronometricMetricField Event Tangent × (Event → ℝ) → Source}
    (hg₁ : GaugeInvariant (fun (c : ℝ) (phi : Event → ℝ) => fun x => c + phi x) law₁)
    (hg₂ : GaugeInvariant (fun (c : ℝ) (phi : Event → ℝ) => fun x => c + phi x) law₂) :
    chronometricSolutionGraph
          (reporterCompleteEncode ChronometricMetricField.squaredInterval potentialReporter)
          law₁ =
        chronometricSolutionGraph
          (reporterCompleteEncode ChronometricMetricField.squaredInterval potentialReporter)
          law₂ ↔
      law₁ = law₂ :=
  chronometricGaugeRigidity ChronometricMetricField.squaredInterval_injective
    potentialReporter_complete hg₁ hg₂

end Potential

/-! ## The reported and the clock-dark sector are genuinely different -/

/-- **Reporting the extra sector is what saves rigidity.** With the sector reported up to gauge,
gauge-invariant laws are rigid; with the sector unreported, laws separating it have identical
graphs. The two statements are about the same geometry space. -/
theorem gauge_dichotomy
    {Metric : Type u} {Extra : Type u} {MetricObs : Type u}
    [Nonempty Metric] {enc : Metric → MetricObs} {e₀ e₁ : Extra} (hne : e₀ ≠ e₁) :
    ∃ law₁ law₂ : Metric × Extra → Prop,
      chronometricSolutionGraph
            (reporterCompleteEncode enc (fun _ : Extra => PUnit.unit)) law₁ =
          chronometricSolutionGraph
            (reporterCompleteEncode enc (fun _ : Extra => PUnit.unit)) law₂ ∧
        law₁ ≠ law₂ := by
  refine exists_ne_law_graph_eq_of_not_injective ?_
  intro hinj
  obtain ⟨g⟩ := ‹Nonempty Metric›
  have := hinj (a₁ := (g, e₀)) (a₂ := (g, e₁)) rfl
  exact hne (congrArg Prod.snd this)

end GaloisForLFunctions.HTGeometry
