#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
lake env lean verification/AuditAll.lean
lake env lean verification/SubmissionAudit.lean
