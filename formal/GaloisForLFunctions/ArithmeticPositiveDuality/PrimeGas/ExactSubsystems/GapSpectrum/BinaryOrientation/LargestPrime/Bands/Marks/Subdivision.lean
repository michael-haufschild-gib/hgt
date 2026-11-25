import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.CountLaw

/-! # Independent colored readings on adjacent prime-energy bands -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks

open Filter Topology Set MeasureTheory _root_.RHTower

/-- Two tests with a sharp change of mark at the common endpoint. -/
def paste (b : ℝ) (f g : ℝ → ℂ) (v : ℝ) := if v ≤ b then f v else g v

private theorem euler_paste {c b d : ℝ} (hcb : c ≤ b) (hbd : b ≤ d) (h : Ioi (0:ℝ)) (f g : ℝ → ℂ) :
    euler c d h (paste b f g) = euler c b h f*euler b d h g := by
  have hU : added c d h = added c b h ∪ added b d h := by
    ext p
    simp only [Finset.mem_union,mem_added]
    constructor
    · rintro ⟨hc,hd⟩
      rcases le_or_gt (location h p) b with hb | hb
      · exact Or.inl ⟨hc,hb⟩
      · exact Or.inr ⟨hb,hd⟩
    · rintro (⟨hc,hb⟩ | ⟨hb,hd⟩)
      · exact ⟨hc,hb.trans hbd⟩
      · exact ⟨hcb.trans_lt hb,hd⟩
  have hD : Disjoint (added c b h) (added b d h) := Finset.disjoint_left.mpr fun p h₁ h₂ =>
    (not_lt.mpr ((mem_added _ _ _ _).mp h₁).2) ((mem_added _ _ _ _).mp h₂).1
  unfold euler
  rw [hU,Finset.prod_union hD]
  congr 1
  · exact Finset.prod_congr rfl fun p hp => by simp [paste,((mem_added _ _ _ _).mp hp).2]
  · exact Finset.prod_congr rfl fun p hp => by simp [paste,not_le.mpr ((mem_added _ _ _ _).mp hp).1]

/-- Exact independence of two prime-dependent marks read from one upper-band configuration. -/
theorem reading_paste {c b d : ℝ} (hcb : c ≤ b) (hbd : b ≤ d) (h : Ioi (0:ℝ)) (a : ℝ) (f g : ℝ → ℂ) :
    reading (added c d h) (1+a*h.val) h (paste b f g) =
      reading (added c b h) (1+a*h.val) h f*reading (added b d h) (1+a*h.val) h g := by
  have hnum : (fun v => paste b f g v*tilt a v) =
      paste b (fun v => f v*tilt a v) (fun v => g v*tilt a v) := by
    funext v
    by_cases hv : v ≤ b <;> simp [paste,hv]
  have hden : paste b (tilt a) (tilt a) = tilt a := by funext v; simp [paste]
  simp only [reading_eq,hnum,euler_paste hcb hbd]
  have hZ := euler_paste hcb hbd h (tilt a) (tilt a)
  rw [hden] at hZ
  rw [hZ,mul_div_mul_comm]

/-- The limiting marked reading factorizes even when the two continuous tests disagree at the boundary. -/
theorem paste_limit {c b d : ℝ} (hc : 0 < c) (hcb : c < b) (hbd : b < d) (a : ℝ)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    Tendsto (fun h => reading (added c d h) (1+a*h.val) h (paste b f g)) criticalApproach
      (𝓝 (Complex.exp (exponent c b a f)*Complex.exp (exponent b d a g))) :=
  ((reading_limit hc hcb a f hf).mul (reading_limit (hc.trans hcb) hbd a g hg)).congr
    (fun h => (reading_paste hcb.le hbd.le h a f g).symm)

private theorem left_subset {c b d : ℝ} (hbd : b ≤ d) (h : Ioi (0:ℝ)) :
    added c b h ⊆ added c d h := by
  intro p hp
  have hv := (mem_added _ _ _ _).mp hp
  exact (mem_added _ _ _ _).mpr ⟨hv.1,hv.2.trans hbd⟩

private theorem right_packet {c b d : ℝ} (hcb : c ≤ b) (h : Ioi (0:ℝ)) :
    added c d h \ added c b h = added b d h := by
  ext p
  simp only [Finset.mem_sdiff,mem_added]
  constructor
  · rintro ⟨⟨hc,hd⟩,hn⟩
    exact ⟨lt_of_not_ge (fun hb => hn ⟨hc,hb⟩),hd⟩
  · rintro ⟨hb,hd⟩
    exact ⟨⟨hcb.trans_lt hb,hd⟩,fun h => (not_le.mpr hb) h.2⟩

/-- Both count coordinates are read from a single occupation configuration on the union. -/
def pairedCount {c b d : ℝ} (hbd : b ≤ d) (h : Ioi (0:ℝ)) (s : ℝ) : ProbabilityMeasure (ℝ × ℝ) :=
  observed (added c d h) s fun x =>
    let y := splitBits (left_subset hbd h) x
    (((squarefreeOccupationFinset y.1).card:ℝ),((squarefreeOccupationFinset y.2).card:ℝ))

theorem pairedCount_eq {c b d : ℝ} (hcb : c ≤ b) (hbd : b ≤ d) (h : Ioi (0:ℝ)) (s : ℝ) :
    pairedCount (c := c) hbd h s = (countLaw c b h s).prod (countLaw b d h s) := by
  let law (S : Finset Nat.Primes) := observed S s fun x => ((squarefreeOccupationFinset x).card:ℝ)
  have he := observed_split (left_subset (c := c) hbd h) s
    (fun x => ((squarefreeOccupationFinset x).card:ℝ)) (fun y => ((squarefreeOccupationFinset y).card:ℝ))
  change pairedCount hbd h s = (law (added c b h)).prod (law (added c d h \ added c b h)) at he
  rwa [right_packet hcb h] at he

/-- Adjacent counts converge jointly to independent Poisson variables at every thermal drift. -/
theorem pairedCount_limit {c b d : ℝ} (hc : 0 < c) (hcb : c < b) (hbd : b < d) (a : ℝ) :
    Tendsto (fun h => pairedCount (c := c) hbd.le h (1+a*h.val)) criticalApproach
      (𝓝 ((poissonCount ⟨VacuumCalibration.mass c b a,mass_nonneg hc hcb.le a⟩).prod
        (poissonCount ⟨VacuumCalibration.mass b d a,mass_nonneg (hc.trans hcb) hbd.le a⟩))) := by
  have H := ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    ((count_weak_limit hc hcb a).prodMk_nhds (count_weak_limit (hc.trans hcb) hbd a))
  exact H.congr (fun h => (pairedCount_eq hcb.le hbd.le h _).symm)

#print axioms reading_paste
#print axioms paste_limit
#print axioms pairedCount_eq
#print axioms pairedCount_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks
