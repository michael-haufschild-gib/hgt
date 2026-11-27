import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # Budget-dependent first passages through a power-law gate floor -/
open MeasureTheory Filter Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks
noncomputable section
private abbrev frozen (ω : PathPauliDisorder) (n : ℕ) :
    selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
  ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩

/-- A power-law gate excess above one sweep bounds the first crossing
after any affordable visit. The sweep compiler supplies the lower bound
on its squared lag. -/
theorem first_passage_of_power_band (s : ℕ→ℝ) {p : ℕ} (hp : p≠0)
    {b : ℝ} (hb : 0<b) (hband : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      0<s n ∧ s n≤1 ∧ ∀ t∈Icc (s n) 1, ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) k
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        (1+b*t^p)*((n+1:ℕ):ℝ)<(k:ℝ)) :
    ∃ L>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      ∀ (v : ℝ) (r q : ℕ), let m : ℝ := (2*r+q:ℕ)
        m≤b*N →
        HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution (frozen ω n).val v) →
        ∀ ρ∈Icc (9/80:ℝ) (1/8),
          let τ := firstExcessAfter ω n (r+q) v ρ
          let f (x : ℝ) := orbitCircuitDistance (frozen ω n) (n+1+(r+q)) (v+x)
          τ∈Icc 0 1 ∧ τ^p≤ max ((s n)^p) (m/(b*N)) ∧ L≤((n+2:ℕ):ℝ)*τ^2 ∧
            f τ=ρ ∧ ∀ x∈Ico 0 τ, f x<ρ := by
  obtain ⟨_,M,_,hM,hmass⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨1/(6720*M),by positivity,?_⟩
  filter_upwards [hband,hmass] with ω hw hm
  filter_upwards [hw,hm] with n hn hnorm
  intro N v r q m hbudget hv ρ hρ τ f
  let g := m/(b*N)
  let x := g^(1/(p:ℝ))
  let t := max (s n) x
  have hN : 0<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hBN := mul_pos hb hN
  have hg : 0≤g := div_nonneg (Nat.cast_nonneg _) hBN.le
  have hg₁ : g≤1 := (div_le_one hBN).mpr hbudget
  have hx : 0≤x := rpow_nonneg hg _
  have hxp : x^p=g := by
    dsimp only [x]
    rw [←rpow_natCast,←rpow_mul hg]
    rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr hp),rpow_one]
  have hx₁ : x≤1 := by
    by_contra! h
    exact hg₁.not_gt (hxp ▸ one_lt_pow₀ h hp)
  obtain ⟨hs,hs₁,hfit⟩ := hn
  have ht : t∈Icc (s n) 1 := ⟨le_max_left ..,max_le hs₁ hx₁⟩
  have hpay : m≤b*N*t^p := by
    have hh := pow_le_pow_left₀ hx (le_max_right (s n) x) p
    rw [hxp] at hh
    exact ((div_le_iff₀ hBN).mp hh).trans_eq (mul_comm ..)
  have hgap : ¬HasProjectiveCircuitApproximation (n+2) (1/10+ρ) (r+(n+1+(r+q)))
      (unitaryEvolution (frozen ω n).val t) := by
    rintro ⟨z,hz,C,hC,he⟩
    have h := hfit t ht (r+(n+1+(r+q))) ⟨z,hz,C,hC,he.trans (by linarith only [hρ.2])⟩
    change (1+b*t^p)*N<((r+(n+1+(r+q)):ℕ):ℝ) at h
    have hcount : ((r+(n+1+(r+q)):ℕ):ℝ)=N+m := by dsimp only [N,m]; push_cast; ring
    rw [hcount] at h
    linarith only [h,hpay]
  obtain ⟨ht₀,ht',hf,hpre⟩ := firstExcessAfter_le_of_increment ω n r q (hs.le.trans ht.1)
    (show 1/10<ρ by linarith only [hρ.1]) hv hgap
  have hu : τ^p≤ max ((s n)^p) g := by
    apply (pow_le_pow_left₀ ht₀ ht' p).trans
    change (max (s n) x)^p≤_
    rcases le_total (s n) x with h|h
    · rw [max_eq_right h,hxp]
      exact le_max_right ..
    · rw [max_eq_left h]
      exact le_max_left ..
  let u := pathPauliDisorderShell ω n
  let E := τ^2*(84*‖u‖^2)
  obtain ⟨z,hz,C,hC,herr⟩ := BondProducts.bond_sweep_error u τ ht₀ 1 one_pos
  have hi : HasProjectiveCircuitApproximation (n+2) E (n+1) (unitaryEvolution (frozen ω n).val τ) :=
    ⟨z,hz,C,by simpa only [one_mul] using hC.le,by simpa only [Nat.cast_one,div_one] using herr⟩
  obtain ⟨z',hz',D,hD,he'⟩ := affordable_add_time (frozen ω n) (x:=v) (y:=τ) hv hi
  have hd : f τ≤1/10+E := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp
    ⟨z',hz',D,hD.trans (by omega),he'⟩
  change f τ=ρ at hf
  rw [hf] at hd
  have hquad := mul_le_mul_of_nonneg_left hnorm.2 (sq_nonneg τ)
  change τ^2*‖u‖^2≤_ at hquad
  refine ⟨⟨ht₀,ht'.trans ht.2⟩,hu,(div_le_iff₀ (show 0<6720*M by positivity)).mpr ?_,hf,hpre⟩
  dsimp only [E] at hd
  linarith only [hρ.1,hd,hquad]

#print axioms first_passage_of_power_band
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
