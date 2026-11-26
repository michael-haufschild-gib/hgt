import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.PhysicalRate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.SeamRate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # Inverse-power disorder bound throughout the physical time range -/

open MeasureTheory ProbabilityTheory Real Filter Set
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section

/-- Coordinates of the unnumbered physical prefix have product Gaussian law. -/
theorem prefix_measure (n : ℕ) :
    MeasurePreserving (fun ω => fun l : PathLabel n => pathPauliDisorderShell ω n l)
      pathPauliDisorderLaw (Measure.pi fun _ => gaussianReal 0 1) := by
  let e := pathCoeffEquiv n
  have h := (measurePreserving_piCongrLeft (fun _ : PathLabel n => gaussianReal 0 1) e).comp
    (gaussian_pauli_prefix_coordinates_law n)
  convert h using 1
  funext ω l
  obtain ⟨i,rfl⟩ := e.surjective l
  simp only [Function.comp_apply,MeasurableEquiv.piCongrLeft_apply_apply,e]

/-- A large number of packets pays for an arbitrary polynomial grid
while allowing dates of order K/(log K)². -/
theorem gaussian_packet_date_tail {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    ∃ τ>0, ∃ t₀>0, ∃ δ>0, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      ∀ t∈Icc t₀ (δ*K/(log K)^2),
      let X := affordableDraw n ⌊τ*K⌋₊ (5/16) t ∩ globalBounds n (u*K) (v*K)
      pathPauliDisorderLaw.real ((fun ω => fun l => pathPauliDisorderShell ω n l) ⁻¹' X)≤2/K^6 := by
  obtain ⟨B,hB,hseam⟩ := exists_seam_rate
  obtain ⟨τ,hτ,c,hc,t₀,ht₀,η,hη,U,V,h ⟩ := physical_packet_rate hu hv hB
  let d := min c 1
  have hd : 0<d := lt_min hc zero_lt_one
  let M := 6/d
  have hM : 0<M := div_pos (by norm_num) hd
  let δ := η/(4*M^2)
  have hδ : 0<δ := div_pos hη (by positivity)
  refine ⟨τ,hτ,t₀,ht₀,δ,hδ,?_⟩
  have hl := (tendsto_add_atTop_nat 2).eventually (eventual_balanced_length hM U (max 1 V))
  filter_upwards [hl] with n hn
  intro K t ht X
  let L := ⌊K/(M*log K)⌋₊
  let q := K/L
  let T := seamNeighbourhood (SpectralGapMass.Bulk.PeriodicCuts.labels (n:=n) L none)
  let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
  obtain ⟨hL,hU,hq,hqlo,hqhi⟩ := hn
  have hK : 1<K := by dsimp only [K]; exact_mod_cast (by omega : 1<n+2)
  have hlog := log_pos hK
  have hLp : (0:ℝ)<L := Nat.cast_pos.mpr hL
  have hq₁ : 1≤q := (le_max_left ..).trans hq
  have hqp := zero_lt_one.trans_le hq₁
  have hrec : q*(L:ℝ)=K := div_mul_cancel₀ _ hLp.ne'
  have htime : t≤η*L/q := by
    apply ht.2.trans
    apply (le_div_iff₀ hqp).mpr
    have hs := sq_le_sq' (show -(2*(M*log K))≤q by linarith only [hq₁,mul_pos hM hlog]) hqhi
    have hratio : q^2/(4*(M*log K)^2)≤1 := (div_le_one (by positivity)).mpr (by linarith only [hs])
    calc
      δ*K/(log K)^2*q = η*(L:ℝ)*(q^2/(4*(M*log K)^2)) := by
        dsimp only [δ]
        nth_rw 1 [←hrec]
        field_simp
      _ ≤ η*(L:ℝ)*1 := mul_le_mul_of_nonneg_left hratio (mul_nonneg hη.le hLp.le)
      _ = _ := mul_one _
  have hc' := h n L hU ((le_max_right ..).trans hq) t ht.1 htime
  have hb := hseam hL hq₁ (n:=n)
  have hs := split_probability (s:=⌊τ*K⌋₊) T (u*K) (v*K) (B*q) (5/16) t
  have he : exp (-d*q)≤1/K^6 := by
    have hx := mul_le_mul_of_nonneg_left hqlo hd.le
    have hdM : d*M=6 := by dsimp only [M]; field_simp
    have hy : 6*log K≤d*q := by rwa [←mul_assoc,hdM] at hx
    apply (exp_le_exp.mpr (show -d*q≤-(6*log K) by linarith only [hy])).trans_eq
    rw [exp_neg,show (6:ℝ)*log K=(6:ℕ)*log K by norm_num,exp_nat_mul,exp_log (zero_lt_one.trans hK),one_div]
  have hp : μ.real X≤2/K^6 := by
    apply hs.trans
    have h₁ := hc'.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (neg_le_neg (min_le_left c 1)) hqp.le))
    have h₂ := hb.trans (exp_le_exp.mpr (show -q≤ -d*q by
      linarith only [mul_le_mul_of_nonneg_right (min_le_right c 1) hqp.le]))
    exact (add_le_add (h₁.trans he) (h₂.trans he)).trans_eq (by ring)
  have hX : MeasurableSet X := (measurable_affordableDraw ..).inter (measurable_globalBounds ..)
  unfold Measure.real
  rw [(prefix_measure n).measure_preimage hX.nullMeasurableSet]
  exact hp

#print axioms gaussian_packet_date_tail
end
end GaloisForLFunctions.HTGeometry.BlockDilations
