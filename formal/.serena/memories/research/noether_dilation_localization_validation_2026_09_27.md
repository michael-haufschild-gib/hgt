# Final validation/cleanup for dilation-source localization

Companion: `mem:research/noether_dilation_uniform_bound_and_mobius_localization_2026_09_27`.

All 7 new leaves passed targeted foreground `lake --old env lean` checks, each wrote a fresh .olean. Final imported audit checked all 29 public theorem axiom sets: only propext, Classical.choice, Quot.sound; exit 0. All seven have exactly one direct RHTower umbrella import and own object timestamps >= source timestamps. Source scan found no sorry, custom axiom, native_decide, #eval, maxHeartbeats. Final scoped git diff --check passed. No full or umbrella build. No commit/push.

Global lint --check-generated failed with unrelated concurrent unimported modules: CCMQuantileDisplacementMass, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, MoebiusMollifiedZetaField, ZetaZeroDensityPowerSaving. Also LEAN_API and LEAN_OVERVIEW stale due concurrent edits. Did not wire unrelated unfinished files. Metadata/index refreshed again after lint; see command output for completion.

Cleanup COMPLETED: removed own /Users/michael/Documents/Codex/2026-09-26/new-chat-2/work/AuditDilationBound.lean and entire dilation-import-cache hard-link fallback. Original build objects retained. All own Lean processes ended. Earlier memory's cleanup TODO is now resolved.

Goal remains active. Full signed square-root deficit bound and RH remain unproved. Main new actual estimates: |R(T)|<=7/2; |R(T)-L|<=exp(-T)(T+14)/4; centered diagonal<=49/4; complete transient sum for n<=exp(T/2) bounded by (T+14)/4. Exact remaining combined source is Explicit(T)+L*sum_{n<=expT}mu(n)+Tail(T), where Tail runs exp(T/2)<n<=expT. D differs from that entire combined source by at most (T+14)/4. Do not discard any of its three pieces or assert they separately satisfy square-root bounds.
