# Kobra Max LAN — Quick Guide

Kobra Max LAN is a community plugin for OrcaSlicer 2.5 that connects to a stock Anycubic Kobra 3 Max over its proprietary local network protocol. It adds a **Kobra Max** dashboard and printer-agent support for sending sliced jobs, viewing printer status, and operating supported controls without an Anycubic cloud login.

This build was prepared for firmware **V2.5.2.8**, printer address **192.168.0.37**, and two ACE Pro units. It uses your existing slicing profiles; it does not install or replace them.

## Setup

1. Put the printer in **LAN-only mode** and connect your computer to the same network.
2. In OrcaSlicer’s **Plugins** window, choose **Install local plugin** and select `kobra3max_lan.py`. Allow the requested local-network and background-thread permissions.
3. Open the **Kobra Max** tab and check that it shows **Connected** and live temperatures.
4. For native Send/Print support, enable **Preferences → Developer → Use printer agents instead of print hosts**, if required by your Orca build. Select **Kobra 3 Max LAN** as the printer agent in your printer connection settings and use the printer’s IP address.
5. In the plugin’s **Config**, set `nozzle_diameter` to the physically installed nozzle size. This must also match your slicing profile—for example, `0.6` for a 0.6 mm nozzle.

Install updates or reload the plugin when the printer is idle. Reloading replaces the plugin’s connection session.

## Slice and print

1. Choose your working Kobra 3 Max printer, nozzle, filament, and process profiles in OrcaSlicer.
2. In the Kobra Max dashboard, select the correct **Feed source** while idle:
   - **External spool:** for a supported external-feed configuration.
   - **ACE Pro — mapped slots:** for filament routed through the ACE units.
3. Slice the plate and use Orca’s **Send/Print** dialog. For ACE printing, review the filament-to-slot mapping before sending the job.
4. Watch the dashboard and printer for confirmation that the job actually starts. A successful upload or “command sent” message alone does not confirm that firmware accepted the print.

**External spool limitation:** This stock firmware may reject external-spool printing while ACE units are connected. Selecting External spool in the plugin does not override the printer’s physical-feed restrictions. Use a configuration supported by the printer.

### Upload an exported file

Open **Printer files**, choose an exported `.gcode` or `.gcode.3mf` file, and click **Upload only**. Uploading does not start a print. Refresh the file list to check that the file is present.

The dashboard’s file-print action is for external-spool jobs. Use Orca’s native print dialog for ACE jobs that need slot mapping.

## Status and controls

- **Printing progress:** shows the filename, percentage, layers, elapsed time, remaining time, and estimated finish in your computer’s local time. Last-known values remain visible between reports; retained estimates are labeled when no active job report is available.
- **Pause / Resume / Cancel print:** send the corresponding job command. Cancel requires confirmation.
- **Temperature & fan:** enter a nozzle temperature, bed temperature, or part-fan percentage and click the adjacent **Set** button. Live readings do not overwrite values you are editing.
- **Speed:** choose **Standard**, **Sport**, or **Silent** during a print. The selected indicator follows printer reports rather than assuming the command succeeded.
- **Appearance:** choose **Light**, **Dark**, or **System** from the header.

Time estimates come from the printer and can change with print conditions. They are estimates, not guaranteed completion times.

## Camera and light

Click **Open camera** to start the live viewer. Use the **Height** slider or the video area’s vertical resize grip to adjust its size. The full frame fits without cropping; black bars may appear to preserve its proportions.

Use the separate **Camera light On / Off** buttons to control the camera light. **Close viewer** closes this plugin’s video connection without intentionally stopping another viewer such as Anycubic Next.

The viewer catches up when playback falls behind and makes up to five reconnect attempts after stream errors or prolonged stalls. If it stops recovering, close and reopen it. Streaming still depends on the camera, printer firmware, Wi-Fi, and the computer running Orca.

## ACE Pro filament cards

The dashboard shows four slots per ACE: **A1–A4** and **B1–B4**. Each card has a large spool marker, an approximate color name, the exact RGB hex color, material, and reported feed status.

Assigned material and color do **not** prove that filament is physically present or fed to the toolhead. Use the presence/feed labels and check the physical path.

### Correct a manual spool color

1. Wait until the printer is idle.
2. Click **Edit color** on a manually assigned slot.
3. Choose a color or enter a six-digit hex value such as `#FF8000`.
4. Click **Save to printer**.
5. Check that the spool card updates after the printer reports the new color.

This changes the slot’s solid-color assignment while preserving its material type. It does not rewrite an RFID tag. Autodetected, empty, and unknown-assignment slots are protected. Color names are approximations derived from RGB, not manufacturer color names.

Each ACE also has **Dry** and **Stop drying** controls. The current Dry shortcut requests **45°C for four hours** and asks for confirmation.

## Troubleshooting and limits

- **Disconnected:** check power, LAN-only mode, the printer address, and that both devices are on the same network.
- **Print button unavailable:** check printer-agent mode, the selected agent, and the active printer connection.
- **Nozzle mismatch:** match the physical nozzle, Orca profile, and plugin `nozzle_diameter` setting.
- **Firmware refusal:** read the dashboard’s reported error. Check feed source, ACE mapping, and the physical filament path before retrying.
- **Unexpected native Device-page errors or branding:** the custom dashboard is the **Kobra Max** tab. It does not replace Orca’s native Device interface or its placeholders.
- **Progress incorrectly says Done:** use plugin **v0.1.5 or newer**. Older builds could mistake a completed metadata query for a completed print.

This is an unofficial development plugin, not an Anycubic or OrcaSlicer release. Some functions remain subject to hardware validation—particularly ACE color writeback. Raw G-code console and jogging controls are not included in this dashboard. Supervise initial tests and verify physical actions at the printer.
