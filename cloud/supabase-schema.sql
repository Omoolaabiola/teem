-- ============================================================================
-- TEEM Waste Management System v3.0.6 — Supabase Multi-Device Cloud Schema
-- Run this script once in your Supabase SQL Editor (https://supabase.com)
-- to synchronize users, passwords, facilities, payments, evacuations,
-- monthly reports, fleet tracking, and archived documents across all
-- authorized Windows, Netlify Web, and Android devices.
-- ============================================================================

create table if not exists public.teem_sync (
  id text primary key,
  company_name text not null default 'Teem Business Nigeria Enterprises',
  payload jsonb not null default '{}'::jsonb,
  updated_at timestamptz not null default now()
);

alter table public.teem_sync enable row level security;

drop policy if exists "Allow public read/write for TEEM devices" on public.teem_sync;
create policy "Allow public read/write for TEEM devices"
  on public.teem_sync
  for all
  using (true)
  with check (true);

create index if not exists idx_teem_sync_company_name on public.teem_sync (company_name);
create index if not exists idx_teem_sync_updated_at on public.teem_sync (updated_at desc);
