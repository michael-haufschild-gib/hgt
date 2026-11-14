import GaloisForLFunctions.GaloisTheoryOfZeros.SeveralZerosFollowedThroughSimpleZerosAreMovedByOneForwardMonodromy
import GaloisForLFunctions.GaloisTheoryOfZeros.TheNumberOfAZeroInTheOrderOfTheRealLineIsItsStripAtARealSaddle

/-!
# One forward monodromy moves the zeros of one parity of a window down by one

Number the zeros of `H_{1/8}` in the order of the real line (`zeroIndex`). For every `N` there
are `g₁, g₂ ∈ G₊(1/8)` with

* `g₁`: the zero number `k` goes to the zero number `k - 1` for all odd `k` with `|k| ≤ N`
  (`exists_mem_forwardMonodromy_odd_sub_one`),
* `g₂`: the same for all even `k` with `|k| ≤ N`
  (`exists_mem_forwardMonodromy_even_sub_one`).

Proof. Take a real saddle `σ` with the strips of the window and a signed loop of saddles beyond
it. Along the real times from `1/8` to `τ(σ)`, the real saddles and the vertical segment to the
base of the loop, the zero number `k` is followed through simple zeros into the strip `k` at the
base. Around the loop of the sign `ε` the zero of every strip `k` with `cos(πk) = -ε` is followed
through simple zeros into the strip `k - 1`. So along one loop of forward times at `1/8` the zero
number `k` is followed through simple zeros to the zero number `k - 1`, for all these `k` of the
window at once, and one forward monodromy moves several zeros followed through simple zeros.
-/

open Complex MeasureTheory Filter Topology Set Metric
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The path to the base of a loop of saddles -/

/-- The path of times from `1/8` to the time of the saddle `a₀`: the real times up to `τ(σ)`, the
real saddles from `σ` to `Re a₀`, the vertical segment of saddles up to `a₀`. -/
def upPath (σ : ℝ) (a₀ : ℂ) : ℝ → ℂ :=
  pathJoin (timeSeg (1 / 8) (realSaddleTime σ))
    (pathJoin (fun s => saddleTime (realSaddlePath σ a₀.re s))
      (fun s => saddleTime (verticalSaddlePath a₀ s)))

theorem upPath_zero (σ : ℝ) (a₀ : ℂ) : upPath σ a₀ 0 = ((1 / 8 : ℝ) : ℂ) := by
  rw [upPath, pathJoin_zero, timeSeg_zero]

theorem upPath_one (σ : ℝ) (a₀ : ℂ) : upPath σ a₀ 1 = saddleTime a₀ := by
  rw [upPath, pathJoin_one, pathJoin_one]
  show saddleTime (verticalSaddlePath a₀ 1) = saddleTime a₀
  rw [verticalSaddlePath_one]

theorem isForwardTrack_upPath {σ : ℝ} (hσ : 1 ≤ σ) {a₀ : ℂ}
    (hWr : ∀ s, WideRegion (realSaddlePath σ a₀.re s))
    (hWv : ∀ s, WideRegion (verticalSaddlePath a₀ s)) : IsForwardTrack (upPath σ a₀) := by
  have h8 : (1 / 8 : ℝ) ≤ 1 / 8 := le_rfl
  have h₁ := (isForwardPath_timeSeg h8 (eighth_le_realSaddleTime hσ)).track
  have h₂ : IsForwardTrack fun s => saddleTime (realSaddlePath σ a₀.re s) :=
    ⟨(continuous_saddleTime_comp_wide (continuous_realSaddlePath σ a₀.re) hWr).continuousOn,
      fun s _ => (hWr s).time_re_pos⟩
  have h₃ : IsForwardTrack fun s => saddleTime (verticalSaddlePath a₀ s) :=
    ⟨(continuous_saddleTime_comp_wide (continuous_verticalSaddlePath a₀) hWv).continuousOn,
      fun s _ => (hWv s).time_re_pos⟩
  refine h₁.join (h₂.join h₃ ?_) ?_
  · show saddleTime (realSaddlePath σ a₀.re 1) = saddleTime (verticalSaddlePath a₀ 0)
    rw [realSaddlePath_one, verticalSaddlePath_zero]
  · rw [pathJoin_zero, timeSeg_one]
    show (realSaddleTime σ : ℂ) = saddleTime (realSaddlePath σ a₀.re 0)
    rw [realSaddlePath_zero, saddleTime_ofReal]

/-- **The zero number `k` is followed into the strip `k` at the base.** Along the path to a
saddle `a₀` joined to the real saddle `σ` through saddles with the strip facts, a zero that lands
in the strip `k` of the window at `σ` is followed through simple zeros to a zero of the strip `k`
at `a₀`. -/
theorem exists_isSimpleLift_upPath {N : ℕ} {σ : ℝ} (hw : StripWindow (π * (N + 2) + 2) σ)
    {a₀ : ℂ} (hWr : ∀ s, WideRegion (realSaddlePath σ a₀.re s))
    (hFr : ∀ s, StripFacts (π * (N + 2) + 2) (realSaddlePath σ a₀.re s))
    (hWv : ∀ s, WideRegion (verticalSaddlePath a₀ s))
    (hFv : ∀ s, StripFacts (π * (N + 2) + 2) (verticalSaddlePath a₀ s))
    {k : ℤ} (hk1 : -(N : ℤ) - 1 ≤ k) (hk2 : k ≤ N) :
    ∃ U : ℝ → ℂ, IsSimpleLift (upPath σ a₀) U ∧ LandsIn σ (U 0) k ∧
      complexHeat (saddleTime a₀) (U 1) = 0 ∧ a₀ * U 1 ∈ cosStrip (π * k) := by
  have h8 : (1 / 8 : ℝ) ≤ 1 / 8 := le_rfl
  have hT := eighth_le_realSaddleTime hw.one_le
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hθ := sin_pi_mul_int k
  have hθR := abs_pi_mul_int_add_le hk1 hk2
  -- the zero of the strip `k` at `σ` and the lift along the real times that ends at it
  obtain ⟨u, hu, huk⟩ := hw.exists_zero (π * k) hθ hθR
  have hu' : complexHeat ((realSaddleTime σ : ℝ) : ℂ) u = 0 := by rwa [saddleTime_ofReal] at hu
  obtain ⟨W₁, hW₁, hW₁1⟩ := exists_lift_ending_at h8 hT hu'
  -- along the real saddles and up the vertical segment the zero stays in its strip
  obtain ⟨W₂, hW₂, hW₂0, hS₂⟩ := exists_isZeroLift_of_stripFacts
    (continuous_realSaddlePath σ a₀.re) hWr hFr hθ hθR (z₀ := u)
    (by rw [realSaddlePath_zero]; exact hu) (by rw [realSaddlePath_zero]; exact huk)
  have hz₂ : complexHeat (saddleTime (realSaddlePath σ a₀.re 1)) (W₂ 1) = 0 := hW₂.zero 1 h11
  have hs₂ := (hS₂ 1 h11).1
  rw [realSaddlePath_one] at hz₂ hs₂
  obtain ⟨W₃, hW₃, hW₃0, hS₃⟩ := exists_isZeroLift_of_stripFacts
    (continuous_verticalSaddlePath a₀) hWv hFv hθ hθR (z₀ := W₂ 1)
    (by rw [verticalSaddlePath_zero]; exact hz₂)
    (by rw [verticalSaddlePath_zero]; exact openCosStrip_subset _ hs₂)
  have hz₃ : complexHeat (saddleTime (verticalSaddlePath a₀ 1)) (W₃ 1) = 0 := hW₃.zero 1 h11
  have hs₃ := (hS₃ 1 h11).1
  rw [verticalSaddlePath_one] at hz₃ hs₃
  have hL₁ := (isForwardPath_timeSeg h8 hT).isSimpleLift hW₁
  have hL₂ : IsSimpleLift (fun s => saddleTime (realSaddlePath σ a₀.re s)) W₂ :=
    ⟨hW₂, fun s hs => (hS₂ s hs).2⟩
  have hL₃ : IsSimpleLift (fun s => saddleTime (verticalSaddlePath a₀ s)) W₃ :=
    ⟨hW₃, fun s hs => (hS₃ s hs).2⟩
  refine ⟨pathJoin W₁ (pathJoin W₂ W₃),
    hL₁.join (hL₂.join hL₃ hW₃0.symm) (by rw [pathJoin_zero, hW₁1, hW₂0]), ?_, ?_, ?_⟩
  · rw [pathJoin_zero]
    exact ⟨W₁, hW₁, rfl, by rw [hW₁1]; exact huk⟩
  · rw [pathJoin_one, pathJoin_one]
    exact hz₃
  · rw [pathJoin_one, pathJoin_one]
    exact openCosStrip_subset _ hs₃

/-! ## The loop of times at `1/8` -/

/-- The loop of times at `1/8`: to the base of the loop of saddles `a`, around it, and back. -/
def saddleLoopPath (σ : ℝ) (a : ℝ → ℂ) : ℝ → ℂ :=
  pathJoin (upPath σ (a 0)) (pathJoin (fun s => saddleTime (a s)) (pathRev (upPath σ (a 0))))

theorem saddleLoopPath_zero (σ : ℝ) (a : ℝ → ℂ) : saddleLoopPath σ a 0 = ((1 / 8 : ℝ) : ℂ) := by
  rw [saddleLoopPath, pathJoin_zero, upPath_zero]

theorem saddleLoopPath_one (σ : ℝ) (a : ℝ → ℂ) : saddleLoopPath σ a 1 = ((1 / 8 : ℝ) : ℂ) := by
  rw [saddleLoopPath, pathJoin_one, pathJoin_one, pathRev_one, upPath_zero]

/-- **One forward monodromy moves the zeros of the sign `ε` of a window down by one.** For
`ε = ±1` some `g ∈ G₊(1/8)` moves the zero number `k` to the zero number `k - 1`, for all `k`
with `|k| ≤ N` and `cos(πk) = -ε`. -/
theorem exists_mem_forwardMonodromy_zeroIndex_sub_one (N : ℕ) {ε : ℂ} (hε : ε = 1 ∨ ε = -1) :
    ∃ g ∈ forwardMonodromy ((1 / 8 : ℝ) : ℂ) eighth_re_pos eighth_not_mem_branchTimes,
      ∀ p : {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}, -(N : ℤ) ≤ zeroIndex p.1 →
        zeroIndex p.1 ≤ N → (Real.cos (π * zeroIndex p.1) : ℂ) = -ε →
        zeroIndex (g p).1 = zeroIndex p.1 - 1 := by
  obtain ⟨σa, hσa⟩ := exists_stripWindow (π * (N + 2) + 2)
  obtain ⟨σb, hσb⟩ := exists_stripFacts_to_cosineSide (π * (N + 2) + 2)
  obtain ⟨σc, hσc⟩ := exists_exchange_lift (π * (N + 2) + 2)
  obtain ⟨ap, am, hap, ham, hapfar, hamfar⟩ := exists_isSignedLoop (max σb σc)
  -- the signed loop of the sign `ε`, beyond the real saddle `σ`
  obtain ⟨a, hloop, hfar⟩ : ∃ a : ℝ → ℂ, IsSignedLoop ε a ∧ ∀ s, max σb σc ≤ (a s).re := by
    rcases hε with rfl | rfl
    · exact ⟨ap, hap, hapfar⟩
    · exact ⟨am, ham, hamfar⟩
  have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  obtain ⟨σ, hσ1, hσ2⟩ : ∃ σ : ℝ, σa ≤ σ ∧ σb ≤ σ := ⟨max σa σb, le_max_left _ _, le_max_right _ _⟩
  have hw := hσa σ hσ1
  obtain ⟨hWr, hFr, hWv, hFv⟩ := hσb σ hσ2 (a 0) (hloop.region 0).wide
    ((le_max_left _ _).trans (hfar 0)) (hloop.cosineSide hεn)
  have hF₀ : StripFacts (π * (N + 2) + 2) (a 0) := by
    have h := hFv 1
    rwa [verticalSaddlePath_one] at h
  -- the lifts to the base of the loop
  have hup : ∀ k : ℤ, -(N : ℤ) - 1 ≤ k → k ≤ N → ∃ U : ℝ → ℂ,
      IsSimpleLift (upPath σ (a 0)) U ∧ LandsIn σ (U 0) k ∧
        complexHeat (saddleTime (a 0)) (U 1) = 0 ∧ a 0 * U 1 ∈ cosStrip (π * k) :=
    fun k hk1 hk2 => exists_isSimpleLift_upPath hw hWr hFr hWv hFv hk1 hk2
  choose! U hU hUland hUzero hUstrip using hup
  -- the lifts along the loop of times
  have hlift : ∀ k : ℤ, -(N : ℤ) ≤ k → k ≤ N → (Real.cos (π * k) : ℂ) = -ε →
      ∃ L : ℝ → ℂ, IsSimpleLift (saddleLoopPath σ a) L ∧ L 0 = U k 0 ∧ L 1 = U (k - 1) 0 := by
    intro k hk1 hk2 hcos
    have hk1' : -(N : ℤ) - 1 ≤ k := by omega
    have hk3 : -(N : ℤ) - 1 ≤ k - 1 := by omega
    have hk4 : k - 1 ≤ N := by omega
    obtain ⟨w, hwl, hws, hw0, hw1⟩ := hσc hloop hε (fun s => (le_max_right _ _).trans (hfar s))
      (π * k) (sin_pi_mul_int k) hcos (abs_pi_mul_int_add_le hk1' hk2)
    have e : π * ((k - 1 : ℤ) : ℝ) = π * k - π := by
      push_cast
      ring
    have hz0 : complexHeat (saddleTime (a 0)) (w 0) = 0 := hwl.zero 0 ⟨le_rfl, zero_le_one⟩
    have hz1 : complexHeat (saddleTime (a 0)) (w 1) = 0 := by
      have h : complexHeat (saddleTime (a 1)) (w 1) = 0 := hwl.zero 1 ⟨zero_le_one, le_rfl⟩
      rwa [hloop.closed] at h
    -- the ends of the lift around the loop are the zeros of the strips `k` and `k - 1`
    have e0 : U k 1 = w 0 := hF₀.injOn (π * k) (sin_pi_mul_int k)
      (abs_pi_mul_int_add_le hk1' hk2) (U k 1) (w 0) (hUstrip k hk1' hk2) hw0
      (by rw [hUzero k hk1' hk2, hz0])
    have e1 : w 1 = U (k - 1) 1 := by
      have hs := hUstrip (k - 1) hk3 hk4
      have h1 := sin_pi_mul_int (k - 1)
      have h2 := abs_pi_mul_int_add_le hk3 hk4
      rw [e] at hs h1 h2
      exact hF₀.injOn (π * k - π) h1 h2 (w 1) (U (k - 1) 1) hw1 hs
        (by rw [hz1, hUzero (k - 1) hk3 hk4])
    have hLw : IsSimpleLift (fun s => saddleTime (a s)) w := ⟨hwl, hws⟩
    refine ⟨pathJoin (U k) (pathJoin w (pathRev (U (k - 1)))),
      (hU k hk1' hk2).join (hLw.join (hU (k - 1) hk3 hk4).reverse
        (by rw [pathRev_zero]; exact e1)) (by rw [pathJoin_zero]; exact e0),
      pathJoin_zero _ _, ?_⟩
    rw [pathJoin_one, pathJoin_one, pathRev_one]
  choose! L hL hL0 hL1 using hlift
  -- the loop of times is a track of forward times
  have hΓ : IsForwardTrack (saddleLoopPath σ a) := by
    have hupT := isForwardTrack_upPath hw.one_le hWr hWv
    have h₄ : IsForwardTrack fun s => saddleTime (a s) :=
      ⟨(continuous_saddleTime_comp hloop.continuous hloop.region).continuousOn,
        fun s _ => (hloop.region s).time_re_pos⟩
    refine hupT.join (h₄.join hupT.reverse ?_) ?_
    · rw [pathRev_zero, upPath_one]
      exact congrArg saddleTime hloop.closed
    · rw [pathJoin_zero]
      exact upPath_one σ (a 0)
  -- one forward monodromy for all the strips of the sign `ε` of the window
  haveI : Finite {k : ℤ // -(N : ℤ) ≤ k ∧ k ≤ N ∧ (Real.cos (π * k) : ℂ) = -ε} :=
    ((Set.finite_Icc (-(N : ℤ)) N).subset fun k hk => ⟨hk.1, hk.2.1⟩).to_subtype
  have hzeroU : ∀ k : ℤ, -(N : ℤ) - 1 ≤ k → k ≤ N →
      complexHeat ((1 / 8 : ℝ) : ℂ) (U k 0) = 0 := fun k h1 h2 => (hUland k h1 h2).zero
  obtain ⟨P, hP⟩ : ∃ P : {k : ℤ // -(N : ℤ) ≤ k ∧ k ≤ N ∧ (Real.cos (π * k) : ℂ) = -ε} →
      {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}, ∀ i, (P i).1 = U i.1 0 :=
    ⟨fun i => ⟨U i.1 0, hzeroU i.1 (by have := i.2.1; omega) i.2.2.1⟩, fun _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : {k : ℤ // -(N : ℤ) ≤ k ∧ k ≤ N ∧ (Real.cos (π * k) : ℂ) = -ε} →
      {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}, ∀ i, (Q i).1 = U (i.1 - 1) 0 :=
    ⟨fun i => ⟨U (i.1 - 1) 0, hzeroU (i.1 - 1) (by have := i.2.1; omega)
      (by have := i.2.2.1; omega)⟩, fun _ => rfl⟩
  obtain ⟨g, hg, hgP⟩ := exists_mem_forwardMonodromy_of_simple_lifts
    (hb₀ := eighth_re_pos) (hb := eighth_not_mem_branchTimes)
    (w := fun i : {k : ℤ // -(N : ℤ) ≤ k ∧ k ≤ N ∧ (Real.cos (π * k) : ℂ) = -ε} => L i.1) hΓ
    (fun i => hL i.1 i.2.1 i.2.2.1 i.2.2.2) (saddleLoopPath_zero σ a) (saddleLoopPath_one σ a)
    P Q (fun i => (hL0 i.1 i.2.1 i.2.2.1 i.2.2.2).trans (hP i).symm)
    (fun i => (hL1 i.1 i.2.1 i.2.2.1 i.2.2.2).trans (hQ i).symm)
  refine ⟨g, hg, fun p h1 h2 hcos => ?_⟩
  -- a zero with a number of the window is the start of the lift of its strip
  have hland := hw.landsIn_zeroIndex p.2 (by omega) h2
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = zeroIndex p.1 := ⟨_, rfl⟩
  rw [← hk] at h1 h2 hcos hland ⊢
  have hpU : p.1 = U k 0 :=
    hw.eq_of_landsIn (by omega) h2 hland (hUland k (by omega) h2)
  have hPe : P ⟨k, h1, h2, hcos⟩ = p := Subtype.ext ((hP _).trans hpU.symm)
  have h := hgP ⟨k, h1, h2, hcos⟩
  rw [hPe] at h
  rw [h, hQ]
  exact hw.zeroIndex_eq_of_landsIn (by omega) (by omega) (hUland (k - 1) (by omega) (by omega))

/-- **One forward monodromy moves every zero with an odd number of the window down by one.** -/
theorem exists_mem_forwardMonodromy_odd_sub_one (N : ℕ) :
    ∃ g ∈ forwardMonodromy ((1 / 8 : ℝ) : ℂ) eighth_re_pos eighth_not_mem_branchTimes,
      ∀ p : {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}, -(N : ℤ) ≤ zeroIndex p.1 →
        zeroIndex p.1 ≤ N → Odd (zeroIndex p.1) → zeroIndex (g p).1 = zeroIndex p.1 - 1 := by
  obtain ⟨g, hg, h⟩ := exists_mem_forwardMonodromy_zeroIndex_sub_one N (ε := 1) (Or.inl rfl)
  refine ⟨g, hg, fun p h1 h2 hodd => h p h1 h2 ?_⟩
  rw [mul_comm, Real.cos_int_mul_pi, hodd.neg_one_zpow]
  push_cast
  rfl

/-- **One forward monodromy moves every zero with an even number of the window down by one.** -/
theorem exists_mem_forwardMonodromy_even_sub_one (N : ℕ) :
    ∃ g ∈ forwardMonodromy ((1 / 8 : ℝ) : ℂ) eighth_re_pos eighth_not_mem_branchTimes,
      ∀ p : {z : ℂ // complexHeat ((1 / 8 : ℝ) : ℂ) z = 0}, -(N : ℤ) ≤ zeroIndex p.1 →
        zeroIndex p.1 ≤ N → Even (zeroIndex p.1) → zeroIndex (g p).1 = zeroIndex p.1 - 1 := by
  obtain ⟨g, hg, h⟩ := exists_mem_forwardMonodromy_zeroIndex_sub_one N (ε := -1) (Or.inr rfl)
  refine ⟨g, hg, fun p h1 h2 heven => h p h1 h2 ?_⟩
  rw [mul_comm, Real.cos_int_mul_pi, heven.neg_one_zpow]
  push_cast
  rw [neg_neg]

end

end GaloisForLFunctions.GaloisTheoryOfZeros
